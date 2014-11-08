/*-------------------------------------------------------------------------
 *
 * deparse.c
 *		  Query deparser for ppg_fdw
 *
 * This file includes functions that examine query WHERE clauses to see
 * whether they're safe to send to the remote server for execution, as
 * well as functions to construct the query text to be sent.  The latter
 * functionality is annoyingly duplicative of ruleutils.c, but there are
 * enough special considerations that it seems best to keep this separate.
 * One saving grace is that we only need deparse logic for node types that
 * we consider safe to send.
 *
 * We assume that the remote session's search_path is exactly "pg_catalog",
 * and thus we need schema-qualify all and only names outside pg_catalog.
 *
 * We do not consider that it is ever safe to send COLLATE expressions to
 * the remote server: it might not have the same collation names we do.
 * (Later we might consider it safe to send COLLATE "C", but even that would
 * fail on old remote servers.)  An expression is considered safe to send only
 * if all collations used in it are traceable to Var(s) of the foreign table.
 * That implies that if the remote server gets a different answer than we do,
 * the foreign table's columns are not marked with collations that match the
 * remote table's columns, which we can consider to be user error.
 *
 * Portions Copyright (c) 2012-2013, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		  contrib/ppg_fdw/deparse.c
 *
 *-------------------------------------------------------------------------
 */
#include <stdlib.h>
#include "postgres.h"

#include "postgres_fdw.h"
#include "util.h"

#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/sysattr.h"
#include "access/transam.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/var.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/datum.h"



/*
 * Global context for foreign_expr_walker's search of an expression tree.
 */
typedef struct foreign_glob_cxt
{
	PlannerInfo *root;			/* global planner state */
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */
} foreign_glob_cxt;

/*
 * Local (per-tree-level) context for foreign_expr_walker's search.
 * This is concerned with identifying collations used in the expression.
 */
typedef enum
{
	FDW_COLLATE_NONE,			/* expression is of a noncollatable type */
	FDW_COLLATE_SAFE,			/* collation derives from a foreign Var */
	FDW_COLLATE_UNSAFE			/* collation derives from something else */
} FDWCollateState;

typedef struct foreign_loc_cxt
{
	Oid			collation;		/* OID of current collation, if any */
	FDWCollateState state;		/* state of current collation choice */
} foreign_loc_cxt;

/*
 * Context for deparseExpr
 */
typedef struct deparse_expr_cxt
{
	PlannerInfo *root;			/* global planner state */
	Query	*parentParse;
	Query	*curParse;
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */
	StringInfo	buf;			/* output buffer to append to */
	List	  **params_list;	/* exprs that will become remote Params */
	bool orderOnAgg;                 /* wherether  order by an agg tle */   
	bool whereExt;                  /* wherether put where clause to @buf*/
	bool	inJoin;	
} deparse_expr_cxt;

/*
 * Functions to determine whether an expression can be evaluated safely on
 * remote server.
 */
static bool foreign_expr_walker(Node *node,
					foreign_glob_cxt *glob_cxt,
					foreign_loc_cxt *outer_cxt);
static bool is_builtin(Oid procid);

/*
 * Functions to construct string representation of a node tree.
 */
static void deparseSelectSQLIntel(deparse_expr_cxt *context);
static void deparseTargetList(deparse_expr_cxt *context);
static void deparseReturningList(StringInfo buf, PlannerInfo *root,
					 Index rtindex, Relation rel,
					 List *returningList,
					 List **retrieved_attrs);
static void deparseColumnRef(StringInfo buf, int varno, int varattno,
				 deparse_expr_cxt *context);
static void deparseRelation(StringInfo buf, Relation rel);
static void deparseStringLiteral(StringInfo buf, const char *val);
static void deparseExpr(Node *expr, deparse_expr_cxt *context);
static void deparseVar(Var *node, deparse_expr_cxt *context);
static void deparseConst(Const *node, deparse_expr_cxt *context);
static void deparseParam(Param *node, deparse_expr_cxt *context);
static void deparseArrayRef(ArrayRef *node, deparse_expr_cxt *context);
static void deparseFuncExpr(FuncExpr *node, deparse_expr_cxt *context);
static void deparseOpExpr(OpExpr *node, deparse_expr_cxt *context);
static void deparseOperatorName(StringInfo buf, Form_pg_operator opform);
static void deparseDistinctExpr(DistinctExpr *node, deparse_expr_cxt *context);
static void deparseScalarArrayOpExpr(ScalarArrayOpExpr *node,
						 deparse_expr_cxt *context);
static void deparseRelabelType(RelabelType *node, deparse_expr_cxt *context);
static void deparseBoolExpr(BoolExpr *node, deparse_expr_cxt *context);
static void deparseNullTest(NullTest *node, deparse_expr_cxt *context);
static void deparseArrayExpr(ArrayExpr *node, deparse_expr_cxt *context);
static void deparseAgg(Aggref *agg, deparse_expr_cxt *context);
static void deparseFromClause(FromExpr *node,deparse_expr_cxt *context);
static void deparseOrderbyClause(deparse_expr_cxt *context);
static void deparseGroupbyClause(deparse_expr_cxt *context);
static void deparseRangeTblRef(RangeTblRef *node, deparse_expr_cxt *context);
static void deparseJoinExpr(JoinExpr *node, deparse_expr_cxt *context);
static void deparseSortGroupClause(SortGroupClause *node, deparse_expr_cxt *context);
static void deparseHavingClause(deparse_expr_cxt *context);
static void deparseLimitClause(deparse_expr_cxt *context);
static void deparseCaseExpr(CaseExpr *node, deparse_expr_cxt *context);
static void deparseCaseWhen(CaseWhen *node, deparse_expr_cxt *context);
static void deparseQual(Node  *quals, deparse_expr_cxt *context);
static void deparseSubLink(SubLink *node, deparse_expr_cxt *context);
/*
 * Examine each restriction clause in baserel's baserestrictinfo list,
 * and classify them into two groups, which are returned as two lists:
 *	- remote_conds contains expressions that can be evaluated remotely
 *	- local_conds contains expressions that can't be evaluated remotely
 */
void
classifyConditions(PlannerInfo *root,
				   RelOptInfo *baserel,
				   List **remote_conds,
				   List **local_conds)
{
	ListCell   *lc;

	*remote_conds = NIL;
	*local_conds = NIL;

	foreach(lc, baserel->baserestrictinfo)
	{
		RestrictInfo *ri = (RestrictInfo *) lfirst(lc);

		if (is_foreign_expr(root, baserel, ri->clause))
			*remote_conds = lappend(*remote_conds, ri);
		else
			*local_conds = lappend(*local_conds, ri);
	}
}

/*
 * Returns true if given expr is safe to evaluate on the foreign server.
 */
bool
is_foreign_expr(PlannerInfo *root,
				RelOptInfo *baserel,
				Expr *expr)
{
	foreign_glob_cxt glob_cxt;
	foreign_loc_cxt loc_cxt;

	/*
	 * Check that the expression consists of nodes that are safe to execute
	 * remotely.
	 */
	glob_cxt.root = root;
	glob_cxt.foreignrel = baserel;
	loc_cxt.collation = InvalidOid;
	loc_cxt.state = FDW_COLLATE_NONE;
	if (!foreign_expr_walker((Node *) expr, &glob_cxt, &loc_cxt))
		return false;

	/* Expressions examined here should be boolean, ie noncollatable */
	Assert(loc_cxt.collation == InvalidOid);
	Assert(loc_cxt.state == FDW_COLLATE_NONE);

	/*
	 * An expression which includes any mutable functions can't be sent over
	 * because its result is not stable.  For example, sending now() remote
	 * side could cause confusion from clock offsets.  Future versions might
	 * be able to make this choice with more granularity.  (We check this last
	 * because it requires a lot of expensive catalog lookups.)
	 */
	if (contain_mutable_functions((Node *) expr))
		return false;

	/* OK to evaluate on the remote server */
	return true;
}

/*
 * Check if expression is safe to execute remotely, and return true if so.
 *
 * In addition, *outer_cxt is updated with collation information.
 *
 * We must check that the expression contains only node types we can deparse,
 * that all types/functions/operators are safe to send (which we approximate
 * as being built-in), and that all collations used in the expression derive
 * from Vars of the foreign table.	Because of the latter, the logic is
 * pretty close to assign_collations_walker() in parse_collate.c, though we
 * can assume here that the given expression is valid.
 */
static bool
foreign_expr_walker(Node *node,
					foreign_glob_cxt *glob_cxt,
					foreign_loc_cxt *outer_cxt)
{
	bool		check_type = true;
	foreign_loc_cxt inner_cxt;
	Oid			collation;
	FDWCollateState state;

	/* Need do nothing for empty subexpressions */
	if (node == NULL)
		return true;

	/* Set up inner_cxt for possible recursion to child nodes */
	inner_cxt.collation = InvalidOid;
	inner_cxt.state = FDW_COLLATE_NONE;

	switch (nodeTag(node))
	{
		case T_Var:
			{
				Var		   *var = (Var *) node;

				/*
				 * If the Var is from the foreign table, we consider its
				 * collation (if any) safe to use.	If it is from another
				 * table, we treat its collation the same way as we would a
				 * Param's collation, ie it's not safe for it to have a
				 * non-default collation.
				 */
				if (var->varno == glob_cxt->foreignrel->relid &&
					var->varlevelsup == 0)
				{
					/* Var belongs to foreign table */
					collation = var->varcollid;
					state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;
				}
				else
				{
					/* Var belongs to some other table */
					if (var->varcollid != InvalidOid &&
						var->varcollid != DEFAULT_COLLATION_OID)
						return false;

					/* We can consider that it doesn't set collation */
					collation = InvalidOid;
					state = FDW_COLLATE_NONE;
				}
			}
			break;
		case T_Const:
			{
				Const	   *c = (Const *) node;

				/*
				 * If the constant has nondefault collation, either it's of a
				 * non-builtin type, or it reflects folding of a CollateExpr;
				 * either way, it's unsafe to send to the remote.
				 */
				if (c->constcollid != InvalidOid &&
					c->constcollid != DEFAULT_COLLATION_OID)
					return false;

				/* Otherwise, we can consider that it doesn't set collation */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_Param:
			{
				Param	   *p = (Param *) node;

				/*
				 * Collation handling is same as for Consts.
				 */
				if (p->paramcollid != InvalidOid &&
					p->paramcollid != DEFAULT_COLLATION_OID)
					return false;

				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_ArrayRef:
			{
				ArrayRef   *ar = (ArrayRef *) node;;

				/* Assignment should not be in restrictions. */
				if (ar->refassgnexpr != NULL)
					return false;

				/*
				 * Recurse to remaining subexpressions.  Since the array
				 * subscripts must yield (noncollatable) integers, they won't
				 * affect the inner_cxt state.
				 */
				if (!foreign_expr_walker((Node *) ar->refupperindexpr,
										 glob_cxt, &inner_cxt))
					return false;
				if (!foreign_expr_walker((Node *) ar->reflowerindexpr,
										 glob_cxt, &inner_cxt))
					return false;
				if (!foreign_expr_walker((Node *) ar->refexpr,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * Array subscripting should yield same collation as input,
				 * but for safety use same logic as for function nodes.
				 */
				collation = ar->refcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *fe = (FuncExpr *) node;

				/*
				 * If function used by the expression is not built-in, it
				 * can't be sent to remote because it might have incompatible
				 * semantics on remote side.
				 */
				if (!is_builtin(fe->funcid))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) fe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If function's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (fe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 fe->inputcollid != inner_cxt.collation)
					return false;

				/*
				 * Detect whether node is introducing a collation not derived
				 * from a foreign Var.	(If so, we just mark it unsafe for now
				 * rather than immediately returning false, since the parent
				 * node might not care.)
				 */
				collation = fe->funccollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_OpExpr:
		case T_DistinctExpr:	/* struct-equivalent to OpExpr */
			{
				OpExpr	   *oe = (OpExpr *) node;

				/*
				 * Similarly, only built-in operators can be sent to remote.
				 * (If the operator is, surely its underlying function is
				 * too.)
				 */
				if (!is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) oe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Result-collation handling is same as for functions */
				collation = oe->opcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *oe = (ScalarArrayOpExpr *) node;

				/*
				 * Again, only built-in operators can be sent to remote.
				 */
				if (!is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) oe->args,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_RelabelType:
			{
				RelabelType *r = (RelabelType *) node;

				/*
				 * Recurse to input subexpression.
				 */
				if (!foreign_expr_walker((Node *) r->arg,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * RelabelType must not introduce a collation not derived from
				 * an input foreign Var.
				 */
				collation = r->resultcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *b = (BoolExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) b->args,
										 glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_NullTest:
			{
				NullTest   *nt = (NullTest *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) nt->arg,
										 glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_ArrayExpr:
			{
				ArrayExpr  *a = (ArrayExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!foreign_expr_walker((Node *) a->elements,
										 glob_cxt, &inner_cxt))
					return false;

				/*
				 * ArrayExpr must not introduce a collation not derived from
				 * an input foreign Var.
				 */
				collation = a->array_collid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_List:
			{
				List	   *l = (List *) node;
				ListCell   *lc;

				/*
				 * Recurse to component subexpressions.
				 */
				foreach(lc, l)
				{
					if (!foreign_expr_walker((Node *) lfirst(lc),
											 glob_cxt, &inner_cxt))
						return false;
				}

				/*
				 * When processing a list, collation state just bubbles up
				 * from the list elements.
				 */
				collation = inner_cxt.collation;
				state = inner_cxt.state;

				/* Don't apply exprType() to the list. */
				check_type = false;
			}
			break;
		default:

			/*
			 * If it's anything else, assume it's unsafe.  This list can be
			 * expanded later, but don't forget to add deparse support below.
			 */
			return false;
	}

	/*
	 * If result type of given expression is not built-in, it can't be sent to
	 * remote because it might have incompatible semantics on remote side.
	 */
	if (check_type && !is_builtin(exprType(node)))
		return false;

	/*
	 * Now, merge my collation information into my parent's state.
	 */
	if (state > outer_cxt->state)
	{
		/* Override previous parent state */
		outer_cxt->collation = collation;
		outer_cxt->state = state;
	}
	else if (state == outer_cxt->state)
	{
		/* Merge, or detect error if there's a collation conflict */
		switch (state)
		{
			case FDW_COLLATE_NONE:
				/* Nothing + nothing is still nothing */
				break;
			case FDW_COLLATE_SAFE:
				if (collation != outer_cxt->collation)
				{
					/*
					 * Non-default collation always beats default.
					 */
					if (outer_cxt->collation == DEFAULT_COLLATION_OID)
					{
						/* Override previous parent state */
						outer_cxt->collation = collation;
					}
					else if (collation != DEFAULT_COLLATION_OID)
					{
						/*
						 * Conflict; show state as indeterminate.  We don't
						 * want to "return false" right away, since parent
						 * node might not care about collation.
						 */
						outer_cxt->state = FDW_COLLATE_UNSAFE;
					}
				}
				break;
			case FDW_COLLATE_UNSAFE:
				/* We're still conflicted ... */
				break;
		}
	}

	/* It looks OK */
	return true;
}

/*
 * Return true if given object is one of PostgreSQL's built-in objects.
 *
 * We use FirstBootstrapObjectId as the cutoff, so that we only consider
 * objects with hand-assigned OIDs to be "built in", not for instance any
 * function or type defined in the information_schema.
 *
 * Our constraints for dealing with types are tighter than they are for
 * functions or operators: we want to accept only types that are in pg_catalog,
 * else format_type might incorrectly fail to schema-qualify their names.
 * (This could be fixed with some changes to format_type, but for now there's
 * no need.)  Thus we must exclude information_schema types.
 *
 * XXX there is a problem with this, which is that the set of built-in
 * objects expands over time.  Something that is built-in to us might not
 * be known to the remote server, if it's of an older version.  But keeping
 * track of that would be a huge exercise.
 */
static bool
is_builtin(Oid oid)
{
	return (oid < FirstBootstrapObjectId);
}

static void deparseSelectSQLIntel(deparse_expr_cxt *context) 
{
	
	appendStringInfoString(context->buf, "SELECT ");
	deparseTargetList(context);
	if (length(context->curParse->jointree->fromlist) > 0){
		appendStringInfoString(context->buf, " FROM ");
	}
	deparseFromClause(context->curParse->jointree, context);
	deparseGroupbyClause(context);
//	deparseHavingClause(context);
	deparseOrderbyClause(context);
	if (!(context->orderOnAgg)) {
		// Don't push limit clause to remote if order on agg tle
		deparseLimitClause(context);
	}
}
/*
 * Construct a simple SELECT statement from a parse tree
 *
 */
void
deparseSelectSql(StringInfo buf,
				 PlannerInfo *root,
				 RelOptInfo *baserel,
				 Bitmapset *attrs_used)
{
	deparse_expr_cxt context;
	/* Set up context struct for recursion */
	context.root = root;
	context.foreignrel = baserel;
	context.buf = buf;
	context.params_list = NULL;
	context.inJoin = false;
	context.parentParse = root->parse;
	context.curParse = root->parse;
	deparseSelectSQLIntel(&context);
}

static void 
deparseHavingClause(deparse_expr_cxt *context)
{
	Node  *node = context->curParse->havingQual;
	if(node != NULL) {
		StringInfo buf = context->buf;
		bool first = true;
		ListCell   *l;
		appendStringInfoString(buf, " having ");
		if (and_clause(node) || nodeTag(node)== T_List) {
			List	*list = NIL;
			if (nodeTag(node)== T_List) {
				list = node;
			} else {
				list =  ((BoolExpr *) node)->args;
			}
        	foreach(l, list)
        	{
				if (!first) {
					appendStringInfoString(buf, " and ");	
				} else {
					first = false;
				}
				deparseExpr(lfirst(l), context);	
			}
		} else if (or_clause(node)) {
        	foreach(l, ((BoolExpr *) node)->args)
        	{
				if (!first) {
					appendStringInfoString(buf, " or ");	
				} else {
					first = false;
				}
				deparseExpr(lfirst(l), context);	
			}
		}
	}
}

static void 
deparseLimitClause(deparse_expr_cxt *context)
{
	Node  *limitOffset = context->curParse->limitOffset;
	Node  *limitCount = context->curParse->limitCount;
	StringInfo buf = context->buf;
	if ((limitOffset == NULL) && (limitCount == NULL) ) {
		return ;
	}

 	appendStringInfoString(buf, " limit ");

	if (limitOffset != NULL) {
		deparseExpr(limitOffset, context);
		appendStringInfoString(buf, " , ");
	}
	if (limitCount != NULL) {
		deparseExpr(limitCount, context);
	}

}

static void 
deparseFromClause(FromExpr  *jointree, deparse_expr_cxt *context)
{
	StringInfo buf = context->buf;
	ListCell   *lc;
	bool first = true;
	if (length(jointree->fromlist) > 1) {
		context->inJoin = true;
	}
	foreach (lc, jointree->fromlist)
	{	
		if (!first) {
				appendStringInfoString(buf, ", ");
		} else {
				first = false;
		}
		deparseExpr(lfirst(lc), context);
	}
	if(jointree->quals != NULL) {
		StringInfo buf = context->buf;
		context->inJoin = true;
		appendStringInfoString(buf, " where ");
		context->whereExt = true;
		deparseQual(jointree->quals, context);
	}
}

static void 
deparseGroupbyClause(deparse_expr_cxt *context)
{
	StringInfo buf = context->buf;
	SortGroupClause *groupClause = NULL;
	ListCell   *lc;
	ListCell   *lc2;
	bool first ;
	TargetEntry *tle = NULL;
	first = true;
	if (length(context->curParse->groupClause) == 0) {
		return ;
	}
	appendStringInfoString(buf, " group by ");
	foreach (lc, context->curParse->groupClause)
	{	
		groupClause = lfirst(lc);
		foreach (lc2, context->curParse->targetList) 
		{
			tle = lfirst(lc2);
			if (tle->ressortgroupref == groupClause->tleSortGroupRef) {	
				if (!first) {
					appendStringInfoString(buf, ", ");
				} else {
					first = false;
				}
				if(tle->resname != NULL) {
					appendStringInfoString(buf, tle->resname);
					appendStringInfoString(buf, " ");
				} else {
					deparseExpr((Node*)tle->expr, context);
				}
			}
		}
	}
}

static void 
deparseOrderbyClause(deparse_expr_cxt *context)
{
	StringInfo buf = context->buf;
	SortGroupClause *sortClause = NULL;
	ListCell   *lc;
	ListCell   *lc2;
	bool first = true;
	TargetEntry *tle = NULL;
	if (length(context->curParse->sortClause) == 0) {
		return ;
	}
	appendStringInfoString(buf, " order by ");
	foreach (lc, context->curParse->sortClause)
	{	
		sortClause = lfirst(lc);
		foreach (lc2, context->curParse->targetList) 
		{
			tle = lfirst(lc2);
			if (tle->ressortgroupref == sortClause->tleSortGroupRef) {
				if (!first) {
					appendStringInfoString(buf, ", ");
				} else {
					first = false;
				}
				if(tle->resname != NULL) {
					appendStringInfoString(buf, " ");
					appendStringInfoString(buf, tle->resname);
					appendStringInfoString(buf, " ");
				} else {
					deparseExpr((Node*)tle->expr, context);
				}
				if (nodeTag((Node*)tle->expr) == T_Aggref && !(context->orderOnAgg)) {
					context->orderOnAgg = true;	
				}
			}	
		}
		if (sortClause->nulls_first) {
			appendStringInfoString(buf, " DESC ");
		} else {
			appendStringInfoString(buf, " ASC ");
		}
	}
}
/*
 * Emit a target list that retrieves the columns specified in attrs_used.
 * This is used for both SELECT and RETURNING targetlists.
 *
 * The tlist text is appended to buf, and we also create an integer List
 * of the columns being retrieved, which is returned to *retrieved_attrs.
 */
static void
deparseTargetList(deparse_expr_cxt *context)
{
	bool first = true;
	List* targetList = context->curParse->targetList;
	StringInfo buf = context->buf;
	ListCell   *lc = NULL;
	TargetEntry *tle = NULL;
	foreach (lc, targetList)
	{	
		if (!first) {
				appendStringInfoString(buf, ", ");
		} else {
				first = false;
		}
		tle = (TargetEntry *) lfirst(lc);
		deparseExpr((Node*)tle->expr, context);
		if(tle->resname != NULL) {
			appendStringInfoString(buf, " as \"");
			appendStringInfoString(buf, tle->resname);
			appendStringInfoString(buf, "\" ");
		}
	}
}

static void 
deparseQual(Node  *quals, deparse_expr_cxt *context)
{
	ListCell   *lc;
	bool first = true;
	if(quals != NULL) {
		StringInfo buf = context->buf;
		first = true;
		if (IsA(quals, List) ||IsA(quals, IntList) || IsA(quals, OidList)) {
			foreach (lc, quals) {	
				if (!first) {
					appendStringInfoString(buf, " and ");
				} else {
					first = false;
				}
				if (IsA(lfirst(lc), List) ||IsA(lfirst(lc), IntList) || IsA(lfirst(lc), OidList)) {
					deparseQual(lfirst(lc), context);
				} else {
					deparseExpr(lfirst(lc), context);
				}
			}	
		} else {
			deparseExpr(quals, context);
		}
	}
}
/*
static void
deparseTargetList(StringInfo buf,
				  PlannerInfo *root,
				  Index rtindex,
				  Relation rel,
				  Bitmapset *attrs_used,
				  List **retrieved_attrs)
{
	TupleDesc	tupdesc = RelationGetDescr(rel);
	bool		have_wholerow;
	bool		first;
	int			i;

	*retrieved_attrs = NIL;
	have_wholerow = bms_is_member(0 - FirstLowInvalidHeapAttributeNumber,
								  attrs_used);
	first = true;
	for (i = 1; i <= tupdesc->natts; i++)
	{
		Form_pg_attribute attr = tupdesc->attrs[i - 1];
		if (attr->attisdropped)
			continue;

		if (have_wholerow ||
			bms_is_member(i - FirstLowInvalidHeapAttributeNumber,
						  attrs_used))
		{
			if (!first)
				appendStringInfoString(buf, ", ");
			first = false;

			deparseColumnRef(buf, rtindex, i, root);

			*retrieved_attrs = lappend_int(*retrieved_attrs, i);
		}
	}
	if (bms_is_member(SelfItemPointerAttributeNumber - FirstLowInvalidHeapAttributeNumber,
					  attrs_used))
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		appendStringInfoString(buf, "ctid");

		*retrieved_attrs = lappend_int(*retrieved_attrs,
									   SelfItemPointerAttributeNumber);
	}
	if (first)
		appendStringInfoString(buf, "NULL");
}
*/
/*
 * Deparse WHERE clauses in given list of RestrictInfos and append them to buf.
 *
 * baserel is the foreign table we're planning for.
 *
 * If no WHERE clause already exists in the buffer, is_first should be true.
 *
 * If params is not NULL, it receives a list of Params and other-relation Vars
 * used in the clauses; these values must be transmitted to the remote server
 * as parameter values.
 *
 * If params is NULL, we're generating the query for EXPLAIN purposes,
 * so Params and other-relation Vars should be replaced by dummy values.
 */
void
appendWhereClause(StringInfo buf,
				  PlannerInfo *root,
				  RelOptInfo *baserel,
				  List *exprs,
				  bool is_first,
				  List **params)
{
	deparse_expr_cxt context;
	int			nestlevel;
	ListCell   *lc;

	if (params)
		*params = NIL;			/* initialize result list to empty */

	/* Set up context struct for recursion */
	context.root = root;
	context.foreignrel = baserel;
	context.buf = buf;
	context.params_list = params;

	/* Make sure any constants in the exprs are printed portably */
	nestlevel = set_transmission_modes();

	foreach(lc, exprs)
	{
		RestrictInfo *ri = (RestrictInfo *) lfirst(lc);

		/* Connect expressions with "AND" and parenthesize each condition. */
		if (is_first)
			appendStringInfoString(buf, " WHERE ");
		else
			appendStringInfoString(buf, " AND ");

		appendStringInfoChar(buf, '(');
		deparseExpr((Node*)(ri->clause), &context);
		appendStringInfoChar(buf, ')');

		is_first = false;
	}

	reset_transmission_modes(nestlevel);
}

/*
 * deparse remote INSERT statement
 *
 * The statement text is appended to buf, and we also create an integer List
 * of the columns being retrieved by RETURNING (if any), which is returned
 * to *retrieved_attrs.
 */
void
deparseInsertSql(StringInfo buf, PlannerInfo *root,
				 Index rtindex, Relation rel,
				 List *targetAttrs, List *returningList,
				 List **retrieved_attrs)
{
	AttrNumber	pindex;
	bool		first;
	ListCell   *lc;

	appendStringInfoString(buf, "INSERT INTO ");
	deparseRelation(buf, rel);

	if (targetAttrs)
	{
		appendStringInfoString(buf, "(");

		first = true;
		foreach(lc, targetAttrs)
		{
			int			attnum = lfirst_int(lc);

			if (!first)
				appendStringInfoString(buf, ", ");
			first = false;

			deparseColumnRef(buf, rtindex, attnum, root);
		}

		appendStringInfoString(buf, ") VALUES (");

		pindex = 1;
		first = true;
		foreach(lc, targetAttrs)
		{
			if (!first)
				appendStringInfoString(buf, ", ");
			first = false;

			appendStringInfo(buf, "$%d", pindex);
			pindex++;
		}

		appendStringInfoString(buf, ")");
	}
	else
		appendStringInfoString(buf, " DEFAULT VALUES");

	if (returningList)
		deparseReturningList(buf, root, rtindex, rel, returningList,
							 retrieved_attrs);
	else
		*retrieved_attrs = NIL;
}

/*
 * deparse remote UPDATE statement
 *
 * The statement text is appended to buf, and we also create an integer List
 * of the columns being retrieved by RETURNING (if any), which is returned
 * to *retrieved_attrs.
 */
void
deparseUpdateSql(StringInfo buf, PlannerInfo *root,
				 Index rtindex, Relation rel,
				 List *targetAttrs, List *returningList,
				 List **retrieved_attrs)
{
	AttrNumber	pindex;
	bool		first;
	ListCell   *lc;

	appendStringInfoString(buf, "UPDATE ");
	deparseRelation(buf, rel);
	appendStringInfoString(buf, " SET ");

	pindex = 2;					/* ctid is always the first param */
	first = true;
	foreach(lc, targetAttrs)
	{
		int			attnum = lfirst_int(lc);

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		deparseColumnRef(buf, rtindex, attnum, root);
		appendStringInfo(buf, " = $%d", pindex);
		pindex++;
	}
	appendStringInfoString(buf, " WHERE ctid = $1");

	if (returningList)
		deparseReturningList(buf, root, rtindex, rel, returningList,
							 retrieved_attrs);
	else
		*retrieved_attrs = NIL;
}

/*
 * deparse remote DELETE statement
 *
 * The statement text is appended to buf, and we also create an integer List
 * of the columns being retrieved by RETURNING (if any), which is returned
 * to *retrieved_attrs.
 */
void
deparseDeleteSql(StringInfo buf, PlannerInfo *root,
				 Index rtindex, Relation rel,
				 List *returningList,
				 List **retrieved_attrs)
{
	appendStringInfoString(buf, "DELETE FROM ");
	deparseRelation(buf, rel);
	appendStringInfoString(buf, " WHERE ctid = $1");

	if (returningList)
		deparseReturningList(buf, root, rtindex, rel, returningList,
							 retrieved_attrs);
	else
		*retrieved_attrs = NIL;
}

/*
 * deparse RETURNING clause of INSERT/UPDATE/DELETE
 */
static void
deparseReturningList(StringInfo buf, PlannerInfo *root,
					 Index rtindex, Relation rel,
					 List *returningList,
					 List **retrieved_attrs)
{
	Bitmapset  *attrs_used;

	/*
	 * We need the attrs mentioned in the query's RETURNING list.
	 */
	attrs_used = NULL;
	pull_varattnos((Node *) returningList, rtindex,
				   &attrs_used);

	appendStringInfoString(buf, " RETURNING ");
	/*deparseTargetList(buf, root, rtindex, rel, attrs_used,
					  retrieved_attrs);*/
}

/*
 * Construct SELECT statement to acquire size in blocks of given relation.
 *
 * Note: we use local definition of block size, not remote definition.
 * This is perhaps debatable.
 *
 * Note: pg_relation_size() exists in 8.1 and later.
 */
void
deparseAnalyzeSizeSql(StringInfo buf, Relation rel)
{
	StringInfoData relname;

	/* We'll need the remote relation name as a literal. */
	initStringInfo(&relname);
	deparseRelation(&relname, rel);

	appendStringInfo(buf, "SELECT pg_catalog.pg_relation_size(");
	deparseStringLiteral(buf, relname.data);
	appendStringInfo(buf, "::pg_catalog.regclass) / %d", BLCKSZ);
}

/*
 * Construct SELECT statement to acquire sample rows of given relation.
 *
 * SELECT command is appended to buf, and list of columns retrieved
 * is returned to *retrieved_attrs.
 */
void
deparseAnalyzeSql(StringInfo buf, Relation rel, List **retrieved_attrs)
{
	Oid			relid = RelationGetRelid(rel);
	TupleDesc	tupdesc = RelationGetDescr(rel);
	int			i;
	char	   *colname;
	List	   *options;
	ListCell   *lc;
	bool		first = true;

	*retrieved_attrs = NIL;

	appendStringInfoString(buf, "SELECT ");
	for (i = 0; i < tupdesc->natts; i++)
	{
		/* Ignore dropped columns. */
		if (tupdesc->attrs[i]->attisdropped)
			continue;

		if (!first)
			appendStringInfoString(buf, ", ");
		first = false;

		/* Use attribute name or column_name option. */
		colname = NameStr(tupdesc->attrs[i]->attname);
		options = GetForeignColumnOptions(relid, i + 1);

		foreach(lc, options)
		{
			DefElem    *def = (DefElem *) lfirst(lc);

			if (strcmp(def->defname, "column_name") == 0)
			{
				colname = defGetString(def);
				break;
			}
		}

		appendStringInfoString(buf, quote_identifier(colname));

		*retrieved_attrs = lappend_int(*retrieved_attrs, i + 1);
	}

	/* Don't generate bad syntax for zero-column relation. */
	if (first)
		appendStringInfoString(buf, "NULL");

	/*
	 * Construct FROM clause
	 */
	appendStringInfoString(buf, " FROM ");
	deparseRelation(buf, rel);
}

/*
 * Construct name to use for given column, and emit it into buf.
 * If it has a column_name FDW option, use that instead of attribute name.
 */
static void
deparseColumnRef(StringInfo buf, int varno, int varattno, deparse_expr_cxt *context)
{
	RangeTblEntry *rte;
	char	   *colname = NULL;
	char	   *relname = NULL;
	List	   *options;
	ListCell   *lc;
	/* varno must not be any of OUTER_VAR, INNER_VAR and INDEX_VAR. */
	Assert(!IS_SPECIAL_VARNO(varno));

	/* Get RangeTblEntry from array in PlannerInfo. */
	rte = rt_fetch(varno, context->curParse->rtable);
	/*
	 * If it's a column of a foreign table, and it has the column_name FDW
	 * option, use that value.
	 */
	/*if (rte->rtekind != RTE_SUBQUERY) {
		options = GetForeignColumnOptions(rte->relid, varattno);
		foreach(lc, options)
		{
			DefElem    *def = (DefElem *) lfirst(lc);

			if (strcmp(def->defname, "column_name") == 0)
			{
				colname = defGetString(def);
				break;
			}
		}
	} else {
		StringInfoData namebuf;
		initStringInfo(&namebuf);
		appendStringInfo(&namebuf, "tmp_table_%s_%ld", rte->alias->aliasname,  random());	
		rte->alias->aliasname = (char*) palloc((strlen(namebuf.data)+1)*sizeof(char));
		memcpy(rte->alias->aliasname, );
	}*/
 	/*
	 * If it's a column of a regular table or it doesn't have column_name FDW
	 * option, use attribute name.
	 */
	
	if (rte->rtekind == RTE_RELATION) {
		colname = get_relid_attribute_name(rte->relid, varattno);
	} else if (rte->rtekind == RTE_SUBQUERY || rte->rtekind == RTE_JOIN) {
		Alias *eref = rte->eref;
		colname = strVal(list_nth(eref->colnames, varattno-1));
	} else {
		elog(ERROR, "does not support this type of range table entry");
	}
 
	if (rte->eref != NULL && rte->rtekind == RTE_SUBQUERY) {
		appendStringInfoString(buf, rte->alias->aliasname);
		appendStringInfoString(buf, ".");
	} else if(rte->rtekind == RTE_RELATION) {
		if (rte->alias == NULL) {
			relname = get_rel_name(rte->relid);
			appendStringInfoString(buf, quote_identifier(relname));
			appendStringInfoString(buf, ".");
		} else if (rte->alias->aliasname != NULL) {
			appendStringInfoString(buf, rte->alias->aliasname);
			appendStringInfoString(buf, ".");
		}
	}
	appendStringInfoString(buf, quote_identifier(colname));
}

/*
 * Append remote name of specified foreign table to buf.
 * Use value of table_name FDW option (if any) instead of relation's name.
 * Similarly, schema_name FDW option overrides schema name.
 */
static void
deparseRelation(StringInfo buf, Relation rel)
{
	ForeignTable *table;
	const char *nspname = NULL;
	const char *relname = NULL;
	ListCell   *lc;

	/* obtain additional catalog information. */
	table = GetForeignTable(RelationGetRelid(rel));

	/*
	 * Use value of FDW options if any, instead of the name of object itself.
	 */
	foreach(lc, table->options)
	{
		DefElem    *def = (DefElem *) lfirst(lc);

		if (strcmp(def->defname, "schema_name") == 0)
			nspname = defGetString(def);
		else if (strcmp(def->defname, "table_name") == 0)
			relname = defGetString(def);
	}

	/*
	 * Note: we could skip printing the schema name if it's pg_catalog, but
	 * that doesn't seem worth the trouble.
	 */
	if (nspname == NULL)
		nspname = get_namespace_name(RelationGetNamespace(rel));
	if (relname == NULL)
		relname = RelationGetRelationName(rel);

	appendStringInfo(buf, "%s.%s",
					 quote_identifier(nspname), quote_identifier(relname));
}

/*
 * Append a SQL string literal representing "val" to buf.
 */
static void
deparseStringLiteral(StringInfo buf, const char *val)
{
	const char *valptr;

	/*
	 * Rather than making assumptions about the remote server's value of
	 * standard_conforming_strings, always use E'foo' syntax if there are any
	 * backslashes.  This will fail on remote servers before 8.1, but those
	 * are long out of support.
	 */
	if (strchr(val, '\\') != NULL)
		appendStringInfoChar(buf, ESCAPE_STRING_SYNTAX);
	appendStringInfoChar(buf, '\'');
	for (valptr = val; *valptr; valptr++)
	{
		char		ch = *valptr;

		if (SQL_STR_DOUBLE(ch, true))
			appendStringInfoChar(buf, ch);
		appendStringInfoChar(buf, ch);
	}
	appendStringInfoChar(buf, '\'');
}

/*
 * Deparse given expression into context->buf.
 *
 * This function must support all the same node types that foreign_expr_walker
 * accepts.
 *
 * Note: unlike ruleutils.c, we just use a simple hard-wired parenthesization
 * scheme: anything more complex than a Var, Const, function call or cast
 * should be self-parenthesized.
 */
static void
deparseExpr(Node *node, deparse_expr_cxt *context)
{
	if (node == NULL)
		return;
	switch (nodeTag(node))
	{
		case T_Var:
			deparseVar((Var *) node, context);
			break;
		case T_Const:
			deparseConst((Const *) node, context);
			break;
		case T_Param:
			deparseParam((Param *) node, context);
			break;
		case T_ArrayRef:
			deparseArrayRef((ArrayRef *) node, context);
			break;
		case T_FuncExpr:
			deparseFuncExpr((FuncExpr *) node, context);
			break;
		case T_OpExpr:
			deparseOpExpr((OpExpr *) node, context);
			break;
		case T_DistinctExpr:
			deparseDistinctExpr((DistinctExpr *) node, context);
			break;
		case T_ScalarArrayOpExpr:
			deparseScalarArrayOpExpr((ScalarArrayOpExpr *) node, context);
			break;
		case T_RelabelType:
			deparseRelabelType((RelabelType *) node, context);
			break;
		case T_BoolExpr:
			deparseBoolExpr((BoolExpr *) node, context);
			break;
		case T_NullTest:
			deparseNullTest((NullTest *) node, context);
			break;
		case T_ArrayExpr:
			deparseArrayExpr((ArrayExpr *) node, context);
			break;
		case T_Aggref:
			deparseAgg((Aggref *) node, context);
			break;
		case T_RangeTblRef:
			deparseRangeTblRef((RangeTblRef *) node, context);
			break;
		case T_JoinExpr:
			deparseJoinExpr((JoinExpr *) node, context);
			break;
		case T_CaseExpr:
			deparseCaseExpr((CaseExpr *) node, context);
			break;
		case T_CaseWhen:
			deparseCaseWhen((CaseWhen *) node, context);
			break;
		case T_FromExpr:
			deparseFromClause((FromExpr *) node, context);
			break;
		case T_SubLink:
			deparseSubLink((SubLink *) node, context);
			break;

		//case T_SortGroupClause:
		//	deparseSortGroupClause((SortGroupClause *) node, context);
		//	break;
		default:
			elog(ERROR, "unsupported expression type for deparse: %d",
				 (int) nodeTag(node));
			break;
	}
}

static void 
deparseSubLink(SubLink *node, deparse_expr_cxt *context)
{
	SubLink *sublink = node;
	if (sublink->subLinkType != EXPR_SUBLINK) {
		elog(ERROR, "unsupported sublink type for deparse ");
		return;
	}
	Query *last = context->curParse;
	bool tmp = context->orderOnAgg;
	bool tmpExt = context->whereExt;
	context->whereExt = false;
	context->curParse = sublink->subselect;
	appendStringInfoString(context->buf, " ( ");
	deparseSelectSQLIntel(context);	
	appendStringInfoString(context->buf, " ) ");
	context->curParse = last;
	context->orderOnAgg = tmp;
	context->whereExt = tmpExt;
}

static void
deparseCaseExpr(CaseExpr *node, deparse_expr_cxt *context)
{
	StringInfo buf = context->buf;
	appendStringInfoString(buf, " case ");
	if (node->arg != NULL) {
		deparseExpr((Node*)node->arg, context);
	}
	ListCell   *lc;
	foreach(lc, node->args) {
		CaseWhen *cwClause = (CaseWhen *) lfirst(lc);
		deparseExpr((Node*)cwClause, context);
	}
	if (node->defresult != NULL) {
		appendStringInfoString(buf, " else ");
		deparseExpr((Node*)(node->defresult), context);
	}
	appendStringInfoString(buf, " end ");
	return ;
}

static void
deparseCaseWhen(CaseWhen *node, deparse_expr_cxt *context)
{
	StringInfo buf = context->buf;
	appendStringInfoString(buf, " when ");
	deparseExpr((Node*)(node->expr), context);
	appendStringInfoString(buf, " then ");
	deparseExpr((Node*)(node->result), context);
	return;
}


static void
deparseSortGroupClause(SortGroupClause *node, deparse_expr_cxt *context)
{
	Index	tleRef = node->tleSortGroupRef - 1;
	Query *parse = context->curParse;
	List *targetList = parse->targetList;
	TargetEntry *tle = (TargetEntry *) list_nth(targetList, tleRef);
	deparseExpr((Node*)tle->expr, context);
}

static void
deparseJoinExpr(JoinExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = NULL;
	ListCell   *lc = NULL;
	bool first = true;
	bool semi = false;
	bool anti = false;
	TargetEntry *tle = NULL;

	deparseExpr((Node*)node->larg, context);
	if (node->rarg == NULL) {
		return ;
	}

	buf = context->buf;
	switch (node->jointype) {
		case JOIN_INNER:
			appendStringInfoString(buf, " inner join ");
			break;
		case JOIN_LEFT:
			appendStringInfoString(buf, " left join ");
			break;
		case JOIN_FULL:
			appendStringInfoString(buf, " ,  ");
			break;
		case JOIN_RIGHT:
			appendStringInfoString(buf, " right join ");
			break;
		case JOIN_SEMI:
			appendStringInfoString(buf, " ");
			semi = true;	
			break;
		case JOIN_ANTI:
			appendStringInfoString(buf, " ");
			anti = true;
			break;
		default:
 			elog(ERROR, "unsupported join type for deparse");
			break;
	}
	if (!semi && !anti) {
		deparseExpr((Node*)node->rarg, context);
	}  

	if (node->usingClause != NULL) {
		appendStringInfoString(buf, " using ( ");
		foreach (lc, node->usingClause)
		{	
			if (!first)
				appendStringInfo(buf, " , ");
			tle = (TargetEntry *) lfirst(lc);
			deparseExpr((Node*)tle->expr, context);
			first = false;
		}
		deparseExpr((Node*)node->quals, context);
		appendStringInfoString(buf, " ) ");
	} else if(node->quals != NULL) {
		if (!semi && !anti) {
			appendStringInfoString(buf, " on ");
			deparseQual((Node*)node->quals, context);
			return;
		}
		if (context->whereExt) {
			appendStringInfoString(buf, " and ");
		} else {
			appendStringInfoString(buf, " where ");
			context->whereExt = true;
		}
		if (semi) {
			appendStringInfoString(buf, " exists (");
		} else if (anti) {
			appendStringInfoString(buf, " not exists (");
		}
		RangeTblEntry *rte = NULL;
		if(IsA((Node*)node->rarg, RangeTblRef)) {
			rte = rt_fetch(((RangeTblRef*)(node->rarg))->rtindex, context->curParse->rtable);;
			if (rte->rtekind == RTE_RELATION) {
				appendStringInfoString(buf, "select * from ");
				char *relname = get_rel_name(rte->relid);
				appendStringInfoString(buf, "public.");
				appendStringInfoString(buf, quote_identifier(relname));			
				if (rte->alias != NULL) {
					appendStringInfoString(buf, " as ");
					appendStringInfoString(buf, rte->alias->aliasname);
					appendStringInfoString(buf, " ");
				}
				appendStringInfoString(buf, " where ");
			} else if (rte->subquery != NULL){
				// for new SQL reset some variables
				context->whereExt = false;
				bool tmp = context->orderOnAgg;
				context->orderOnAgg = false;
				Query * last = context->curParse;
				context->curParse = rte->subquery;
				deparseSelectSQLIntel(context);	
				if (context->whereExt) {
					appendStringInfoString(buf, " and ");
				} else {
					appendStringInfoString(buf, " where ");
				}
				context->curParse = last;
				context->whereExt = true;
				context->orderOnAgg = tmp;
				appendStringInfoString(buf, " and ");
			} else {
 				elog(ERROR, "unsupported range table entry for deparse");
			}
		} else {
			deparseExpr((Node*)node->rarg, context);
		}
		deparseQual((Node*)node->quals, context);
		appendStringInfoString(buf, ") ");
	}
}

static void
deparseRangeTblRef(RangeTblRef * node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	RangeTblEntry *rte;
	char	   *relname = NULL;
	/* Get RangeTblEntry from array in PlannerInfo. */
	rte = rt_fetch(node->rtindex, context->curParse->rtable);
	if (rte->rtekind == RTE_RELATION) {
		relname = get_rel_name(rte->relid);
		//assume all the remote table of public schema, later to fix it 
		appendStringInfoString(buf, "public.");
		appendStringInfoString(buf, quote_identifier(relname));
	} else if (rte->subquery != NIL) {
		/*PlannerInfo *subroot;
		Plan* sub_plan = ppg_subquery_planner(context->root->glob, rte->subquery, context->root, false, 0, &subroot);
		context->root->glob->subplans = lappend(context->root->glob->subplans, sub_plan);
		SubQueryPlan* subplan = (SubQueryPlan*)palloc(sizeof(SubQueryPlan));
		createSubplan(subplan, rte);
		if (context->inJoin) {
			subplan->dmethod = All;
		} else {
			subplan->dmethod = RoundRobin;
		}
		subplan->subplanIndex = list_length(context->root->glob->subplans);
		context->subplan = lappend(context->subplan, subplan); */
		/*Query * last = context->curParse;
		bool tmp = context->orderOnAgg;
		bool tmpExt = context->whereExt;
		context->whereExt = false;
		context->curParse = rte->subquery;
		appendStringInfoString(buf, " ( ");
		deparseSelectSQLIntel(context);	
		appendStringInfoString(buf, " ) ");
		context->curParse = last;
		context->orderOnAgg = tmp;
		context->whereExt = tmpExt;*/
	} else {
		elog(ERROR, "unexpected range table when deparse");
	}
	if (rte->alias != NULL) {	
		appendStringInfo(buf, " %s ", rte->alias->aliasname);
	}
}

static void deparseAgg(Aggref *agg, deparse_expr_cxt *context)
{	
	StringInfo	buf = context->buf;
    	char * aggname = (char*)getFuncName(agg->aggfnoid);
	appendStringInfoString(buf, aggname);
	appendStringInfoString(buf, "(");

	if (agg->aggdistinct) {
		appendStringInfoString(buf, "distinct(");
	}
	if (agg->aggstar) {
		appendStringInfoString(buf, "*");
	} else {
		ListCell   *lc;
		foreach (lc, agg->args)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(lc);
			deparseExpr((Node*)tle->expr, context);
		}
	}
	if (agg->aggdistinct) {
		appendStringInfoString(buf, ")");
	}
	appendStringInfoString(buf, ")");

}
/*
 * Deparse given Var node into context->buf.
 *
 * If the Var belongs to the foreign relation, just print its remote name.
 * Otherwise, it's effectively a Param (and will in fact be a Param at
 * run time).  Handle it the same way we handle plain Params --- see
 * deparseParam for comments.
 */
static void
deparseVar(Var *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	if (//node->varno == context->foreignrel->relid &&
		node->varlevelsup == 0)
	{
		/* Var belongs to foreign table */
		deparseColumnRef(buf, node->varno, node->varattno, context);
	}
	else
	{
		Query *curParse = context->curParse;
		context->curParse = context->parentParse;
		deparseColumnRef(buf, node->varno, node->varattno, context);
		context->curParse = curParse;
	}
}

/*
 * Deparse given constant value into context->buf.
 *
 * This function has to be kept in sync with ruleutils.c's get_const_expr.
 */
static void
deparseConst(Const *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	Oid			typoutput;
	bool		typIsVarlena;
	char	   *extval;
	bool		isfloat = false;
	bool		needlabel;

	if (node->constisnull)
	{
		appendStringInfo(buf, "NULL");
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(node->consttype,
												  node->consttypmod));
		return;
	}

	getTypeOutputInfo(node->consttype,
					  &typoutput, &typIsVarlena);
	extval = OidOutputFunctionCall(typoutput, node->constvalue);

	switch (node->consttype)
	{
		case INT2OID:
		case INT4OID:
		case INT8OID:
		case OIDOID:
		case FLOAT4OID:
		case FLOAT8OID:
		case NUMERICOID:
			{
				/*
				 * No need to quote unless it's a special value such as 'NaN'.
				 * See comments in get_const_expr().
				 */
				if (strspn(extval, "0123456789+-eE.") == strlen(extval))
				{
					if (extval[0] == '+' || extval[0] == '-')
						appendStringInfo(buf, "(%s)", extval);
					else
						appendStringInfoString(buf, extval);
					if (strcspn(extval, "eE.") != strlen(extval))
						isfloat = true; /* it looks like a float */
				}
				else
					appendStringInfo(buf, "'%s'", extval);
			}
			break;
		case BITOID:
		case VARBITOID:
			appendStringInfo(buf, "B'%s'", extval);
			break;
		case BOOLOID:
			if (strcmp(extval, "t") == 0)
				appendStringInfoString(buf, "true");
			else
				appendStringInfoString(buf, "false");
			break;
		default:
			deparseStringLiteral(buf, extval);
			break;
	}

	/*
	 * Append ::typename unless the constant will be implicitly typed as the
	 * right type when it is read in.
	 *
	 * XXX this code has to be kept in sync with the behavior of the parser,
	 * especially make_const.
	 */
	switch (node->consttype)
	{
		case BOOLOID:
		case INT4OID:
		case UNKNOWNOID:
			needlabel = false;
			break;
		case NUMERICOID:
			needlabel = !isfloat || (node->consttypmod >= 0);
			break;
		default:
			needlabel = true;
			break;
	}
	if (needlabel)
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(node->consttype,
												  node->consttypmod));
}

/*
 * Deparse given Param node.
 *
 * If we're generating the query "for real", add the Param to
 * context->params_list if it's not already present, and then use its index
 * in that list as the remote parameter number.
 *
 * If we're just generating the query for EXPLAIN, replace the Param with
 * a dummy expression "(SELECT null::<type>)".	In all extant versions of
 * Postgres, the planner will see that as an unknown constant value, which is
 * what we want.  (If we sent a Param, recent versions might try to use the
 * value supplied for the Param as an estimated or even constant value, which
 * we don't want.)  This might need adjustment if we ever make the planner
 * flatten scalar subqueries.
 *
 * Note: we label the Param's type explicitly rather than relying on
 * transmitting a numeric type OID in PQexecParams().  This allows us to
 * avoid assuming that types have the same OIDs on the remote side as they
 * do locally --- they need only have the same names.
 */
static void
deparseParam(Param *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	if (context->params_list)
	{
		int			pindex = 0;
		ListCell   *lc;

		/* find its index in params_list */
		foreach(lc, *context->params_list)
		{
			pindex++;
			if (equal(node, (Node *) lfirst(lc)))
				break;
		}
		if (lc == NULL)
		{
			/* not in list, so add it */
			pindex++;
			*context->params_list = lappend(*context->params_list, node);
		}

		appendStringInfo(buf, "$%d", pindex);
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(node->paramtype,
												  node->paramtypmod));
	}
	else
	{
		appendStringInfo(buf, "(SELECT null::%s)",
						 format_type_with_typemod(node->paramtype,
												  node->paramtypmod));
	}
}

/*
 * Deparse an array subscript expression.
 */
static void
deparseArrayRef(ArrayRef *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	ListCell   *lowlist_item;
	ListCell   *uplist_item;

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/*
	 * Deparse referenced array expression first.  If that expression includes
	 * a cast, we have to parenthesize to prevent the array subscript from
	 * being taken as typename decoration.	We can avoid that in the typical
	 * case of subscripting a Var, but otherwise do it.
	 */
	if (IsA(node->refexpr, Var))
		deparseExpr((Node*)(node->refexpr), context);
	else
	{
		appendStringInfoChar(buf, '(');
		deparseExpr((Node*)(node->refexpr), context);
		appendStringInfoChar(buf, ')');
	}

	/* Deparse subscript expressions. */
	lowlist_item = list_head(node->reflowerindexpr);	/* could be NULL */
	foreach(uplist_item, node->refupperindexpr)
	{
		appendStringInfoChar(buf, '[');
		if (lowlist_item)
		{
			deparseExpr(lfirst(lowlist_item), context);
			appendStringInfoChar(buf, ':');
			lowlist_item = lnext(lowlist_item);
		}
		deparseExpr(lfirst(uplist_item), context);
		appendStringInfoChar(buf, ']');
	}

	appendStringInfoChar(buf, ')');
}

/*
 * Deparse a function call.
 */
static void
deparseFuncExpr(FuncExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	HeapTuple	proctup;
	Form_pg_proc procform;
	const char *proname;
	bool		use_variadic;
	bool		first;
	ListCell   *arg;

	/*
	 * If the function call came from an implicit coercion, then just show the
	 * first argument.
	 */
	if (node->funcformat == COERCE_IMPLICIT_CAST)
	{
		deparseExpr((Node *) linitial(node->args), context);
		return;
	}

	/*
	 * If the function call came from a cast, then show the first argument
	 * plus an explicit cast operation.
	 */
	if (node->funcformat == COERCE_EXPLICIT_CAST)
	{
		Oid			rettype = node->funcresulttype;
		int32		coercedTypmod;

		/* Get the typmod if this is a length-coercion function */
		(void) exprIsLengthCoercion((Node *) node, &coercedTypmod);

		deparseExpr((Node *) linitial(node->args), context);
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(rettype, coercedTypmod));
		return;
	}

	/*
	 * Normal function: display as proname(args).
	 */
	proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(node->funcid));
	if (!HeapTupleIsValid(proctup))
		elog(ERROR, "cache lookup failed for function %u", node->funcid);
	procform = (Form_pg_proc) GETSTRUCT(proctup);

	/* Check if need to print VARIADIC (cf. ruleutils.c) */
	if (OidIsValid(procform->provariadic))
	{
		if (procform->provariadic != ANYOID)
			use_variadic = true;
		else
			use_variadic = node->funcvariadic;
	}
	else
		use_variadic = false;

	/* Print schema name only if it's not pg_catalog */
	if (procform->pronamespace != PG_CATALOG_NAMESPACE)
	{
		const char *schemaname;

		schemaname = get_namespace_name(procform->pronamespace);
		appendStringInfo(buf, "%s.", quote_identifier(schemaname));
	}

	/* Deparse the function name ... */
	proname = NameStr(procform->proname);
	appendStringInfo(buf, "%s(", quote_identifier(proname));
	/* ... and all the arguments */
	first = true;
	foreach(arg, node->args)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		if (use_variadic && lnext(arg) == NULL)
			appendStringInfoString(buf, "VARIADIC ");
		deparseExpr((Node *) lfirst(arg), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');

	ReleaseSysCache(proctup);
}

/*
 * Deparse given operator expression.	To avoid problems around
 * priority of operations, we always parenthesize the arguments.
 */
static void
deparseOpExpr(OpExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	HeapTuple	tuple;
	Form_pg_operator form;
	char		oprkind;
	ListCell   *arg;

	/* Retrieve information about the operator from system catalog. */
	tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(node->opno));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for operator %u", node->opno);
	form = (Form_pg_operator) GETSTRUCT(tuple);
	oprkind = form->oprkind;

	/* Sanity check. */
	Assert((oprkind == 'r' && list_length(node->args) == 1) ||
		   (oprkind == 'l' && list_length(node->args) == 1) ||
		   (oprkind == 'b' && list_length(node->args) == 2));

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/* Deparse left operand. */
	if (oprkind == 'r' || oprkind == 'b')
	{
		arg = list_head(node->args);
		deparseExpr(lfirst(arg), context);
		appendStringInfoChar(buf, ' ');
	}

	/* Deparse operator name. */
	deparseOperatorName(buf, form);

	/* Deparse right operand. */
	if (oprkind == 'l' || oprkind == 'b')
	{
		arg = list_tail(node->args);
		appendStringInfoChar(buf, ' ');
		deparseExpr(lfirst(arg), context);
	}

	appendStringInfoChar(buf, ')');

	ReleaseSysCache(tuple);
}

/*
 * Print the name of an operator.
 */
static void
deparseOperatorName(StringInfo buf, Form_pg_operator opform)
{
	char	   *opname;

	/* opname is not a SQL identifier, so we should not quote it. */
	opname = NameStr(opform->oprname);

	/* Print schema name only if it's not pg_catalog */
	if (opform->oprnamespace != PG_CATALOG_NAMESPACE)
	{
		const char *opnspname;

		opnspname = get_namespace_name(opform->oprnamespace);
		/* Print fully qualified operator name. */
		appendStringInfo(buf, "OPERATOR(%s.%s)",
						 quote_identifier(opnspname), opname);
	}
	else
	{
		/* Just print operator name. */
		appendStringInfo(buf, "%s", opname);
	}
}

/*
 * Deparse IS DISTINCT FROM.
 */
static void
deparseDistinctExpr(DistinctExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	Assert(list_length(node->args) == 2);

	appendStringInfoChar(buf, '(');
	deparseExpr(linitial(node->args), context);
	appendStringInfoString(buf, " IS DISTINCT FROM ");
	deparseExpr(lsecond(node->args), context);
	appendStringInfoChar(buf, ')');
}

/*
 * Deparse given ScalarArrayOpExpr expression.	To avoid problems
 * around priority of operations, we always parenthesize the arguments.
 */
static void
deparseScalarArrayOpExpr(ScalarArrayOpExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	HeapTuple	tuple;
	Form_pg_operator form;
	Expr	   *arg1;
	Expr	   *arg2;

	/* Retrieve information about the operator from system catalog. */
	tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(node->opno));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for operator %u", node->opno);
	form = (Form_pg_operator) GETSTRUCT(tuple);

	/* Sanity check. */
	Assert(list_length(node->args) == 2);

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, '(');

	/* Deparse left operand. */
	arg1 = linitial(node->args);
	deparseExpr((Node*)arg1, context);
	appendStringInfoChar(buf, ' ');

	/* Deparse operator name plus decoration. */
	deparseOperatorName(buf, form);
	appendStringInfo(buf, " %s (", node->useOr ? "ANY" : "ALL");

	/* Deparse right operand. */
	arg2 = lsecond(node->args);
	deparseExpr((Node*)arg2, context);

	appendStringInfoChar(buf, ')');

	/* Always parenthesize the expression. */
	appendStringInfoChar(buf, ')');

	ReleaseSysCache(tuple);
}

/*
 * Deparse a RelabelType (binary-compatible cast) node.
 */
static void
deparseRelabelType(RelabelType *node, deparse_expr_cxt *context)
{
	deparseExpr((Node*)(node->arg), context);
	if (node->relabelformat != COERCE_IMPLICIT_CAST)
		appendStringInfo(context->buf, "::%s",
						 format_type_with_typemod(node->resulttype,
												  node->resulttypmod));
}

/*
 * Deparse a BoolExpr node.
 *
 * Note: by the time we get here, AND and OR expressions have been flattened
 * into N-argument form, so we'd better be prepared to deal with that.
 */
static void
deparseBoolExpr(BoolExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	const char *op = NULL;		/* keep compiler quiet */
	bool		first;
	ListCell   *lc;

	switch (node->boolop)
	{
		case AND_EXPR:
			op = "AND";
			break;
		case OR_EXPR:
			op = "OR";
			break;
		case NOT_EXPR:
			appendStringInfoString(buf, "(NOT ");
			deparseExpr(linitial(node->args), context);
			appendStringInfoChar(buf, ')');
			return;
	}

	appendStringInfoChar(buf, '(');
	first = true;
	foreach(lc, node->args)
	{
		if (!first)
			appendStringInfo(buf, " %s ", op);
		deparseExpr((Node *) lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ')');
}

/*
 * Deparse IS [NOT] NULL expression.
 */
static void
deparseNullTest(NullTest *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;

	appendStringInfoChar(buf, '(');
	deparseExpr((Node *)node->arg, context);
	if (node->nulltesttype == IS_NULL)
		appendStringInfoString(buf, " IS NULL)");
	else
		appendStringInfoString(buf, " IS NOT NULL)");
}

/*
 * Deparse ARRAY[...] construct.
 */
static void
deparseArrayExpr(ArrayExpr *node, deparse_expr_cxt *context)
{
	StringInfo	buf = context->buf;
	bool		first = true;
	ListCell   *lc;

	appendStringInfoString(buf, "ARRAY[");
	foreach(lc, node->elements)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		deparseExpr(lfirst(lc), context);
		first = false;
	}
	appendStringInfoChar(buf, ']');

	/* If the array is empty, we need an explicit cast to the array type. */
	if (node->elements == NIL)
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(node->array_typeid, -1));
}

void createSubplan(SubQueryPlan* subplan, RangeTblEntry *rte)
{
	Assert(rte->subquery != NULL);
	Query	*query = rte->subquery;
	ListCell	*lc;
	bool		first = true;
	int32		index = 1;
	StringInfoData createbuf;
	StringInfoData insertbuf;
	initStringInfo(&createbuf);
	initStringInfo(&insertbuf);
	appendStringInfo(&createbuf, "create table public.%s (", rte->alias->aliasname);
	appendStringInfo(&insertbuf, "insert into public.%s values(", rte->alias->aliasname);
	subplan->typeID = NIL;
	foreach(lc, query->targetList) {
		TargetEntry *rt = lfirst(lc);
		if (rt->resjunk) {
			continue;
		}
		if (!first) {
			appendStringInfoString(&createbuf, ", ");
			appendStringInfoString(&insertbuf, ", ");
		} else {
			first = false;
		}
		appendStringInfo(&createbuf, "\"%s\" %s", rt->resname, 
			format_type_with_typemod(exprType((Node*)rt->expr), exprTypmod((Node*)rt->expr)));
		appendStringInfo(&insertbuf, "$%d", index);
		subplan->typeID = lappend_oid(subplan->typeID, exprType((Node*)rt->expr));
		index++;
	}
	appendStringInfoString(&createbuf, ")");
	appendStringInfoString(&insertbuf, ")");
	subplan->createTable = (char*) palloc((strlen(createbuf.data)+1)*sizeof(char));
	memcpy(subplan->createTable, createbuf.data, strlen(createbuf.data));
	subplan->createTable[strlen(createbuf.data)] = 0;
	subplan->insertSQL = (char*) palloc((strlen(insertbuf.data)+1)*sizeof(char));
	memcpy(subplan->insertSQL, insertbuf.data, strlen(insertbuf.data));
	subplan->insertSQL[strlen(insertbuf.data)] = 0;
	elog(INFO, "debug subplan create SQL:%s\n insert SQL :%s\n", subplan->createTable, subplan->insertSQL);
}
