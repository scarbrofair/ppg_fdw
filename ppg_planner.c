
#include "postgres.h"

#include <limits.h>
#include <stdlib.h>

#include "catalog/pg_type.h"
#include "catalog/pg_class.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_operator.h"
#include "access/htup_details.h"
#include "executor/executor.h"
#include "executor/nodeAgg.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodes.h"
#include "nodes/parsenodes.h"
#ifdef OPTIMIZER_DEBUG
#include "nodes/print.h"
#endif
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/subselect.h"
#include "optimizer/tlist.h"
#include "parser/analyze.h"
#include "parser/parsetree.h"
#include "parser/parse_func.h"
#include "parser/parse_oper.h"
#include "rewrite/rewriteManip.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "foreign/foreign.h"
#include "foreign/fdwapi.h"

#include "postgres_fdw.h"
#include "ppg_planner.h"
#include "util.h"

/* Expression kind codes for preprocess_expression */
#define EXPRKIND_QUAL			0
#define EXPRKIND_TARGET			1
#define EXPRKIND_RTFUNC			2
#define EXPRKIND_RTFUNC_LATERAL	3
#define EXPRKIND_VALUES			4
#define EXPRKIND_VALUES_LATERAL	5
#define EXPRKIND_LIMIT			6
#define EXPRKIND_APPINFO		7
#define EXPRKIND_PHV			8
typedef struct
{
        List       *outerList;		/* the target list of finnal result*/
        List       *intelList;		/* the target list for data from remote database*/
	List	   *deparseList;          /*just for deparse */
	AttrNumber intelResno;
	AttrNumber outerResno;
} TargetListContext;

typedef struct
{
        Query *parse;
        Node  *currentExpr;
        bool  changed;
} RewriteOrignalTargetContext;


FdwRoutine *FDW_handler = NULL;

static planner_hook_type next_planner_hook = NULL;

static void preprocess_rowmarks(PlannerInfo *root);

static Node *preprocess_expression(PlannerInfo *root, Node *expr, int kind);

static void preprocess_groupclause(PlannerInfo *root);

static void preprocess_qual_conditions(PlannerInfo *root, Node *jtnode);

static bool limit_needed(Query *parse);

static List *make_fullplanTargetList(PlannerInfo *root, List *tlist, AttrNumber **groupColIdx, bool *need_tlist_eval,
									List** havingTlePosition, List**havingTle);

static void locate_grouping_columns(PlannerInfo *root, List *tlist, List *sub_tlist, AttrNumber *groupColIdx);

static Plan *ppg_grouping_planner(PlannerInfo *root, double tuple_fraction);

static void createNewTargetEntryList(TargetListContext *targetListContext, List *targetList);

static TargetEntry *createNewTargetEntry(List *funcname, List *fargs, bool agg_star, bool agg_distinct, bool func_variadic,
	       	bool resjunk, bool is_column, int location, char*colname, AttrNumber resno);

static void updateSortGroupClause (Query *parse, List *newTlist);

static void postProcessSortList(List *sortList, List *newTlist);

static int32 getTlistWidth(List *outerTleList);

static bool opHasAgg (Node *node);

static List *handleSubquery (PlannerInfo *root);

static void rewriteOrignalTargetList (PlannerInfo *root);

static void rewriteOrignalTargetListWalker (RewriteOrignalTargetContext *context);

static ForeignScan *deparsePlan(PlannerInfo *root);


// borrowed from PG src 
static bool limit_needed(Query *parse)
{
	Node       *node;     
        node = parse->limitCount;      
        if (node) {
		if (IsA(node, Const)) {
			if (!((Const *) node)->constisnull) {
				return true;
			}
		} else {         
                        return true;            /* non-constant LIMIT */                                                                                                                                     
		}
        }
        node = parse->limitOffset;     
        if (node) {
		if (IsA(node, Const)) {
			if (!((Const *) node)->constisnull) {
				int64   offset = DatumGetInt64(((Const *) node)->constvalue);
				if (offset > 0) {
					return true;
				}
			}     
                } else {
			return true;
		}
	}
        return false;
}



static void
preprocess_qual_conditions(PlannerInfo *root, Node *jtnode)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		/* nothing to do here */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
			preprocess_qual_conditions(root, lfirst(l));

		f->quals = preprocess_expression(root, f->quals, EXPRKIND_QUAL);
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		preprocess_qual_conditions(root, j->larg);
		preprocess_qual_conditions(root, j->rarg);

		j->quals = preprocess_expression(root, j->quals, EXPRKIND_QUAL);
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}
/*
 * preprocess_expression ------> borrow from the source code of PG
 *		Do subquery_planner's preprocessing work for an expression,
 *		which can be a targetlist, a WHERE clause (including JOIN/ON
 *		conditions), a HAVING clause, or a few other things.
 */
static Node *
preprocess_expression(PlannerInfo *root, Node *expr, int kind)
{
	if (expr == NULL)
		return NULL;

	if (root->hasJoinRTEs &&
		!(kind == EXPRKIND_RTFUNC || kind == EXPRKIND_VALUES))
		expr = flatten_join_alias_vars(root, expr);

	/*
	 * Simplify constant expressions.
	 */
	expr = eval_const_expressions(root, expr);

	/*
	 * If it's a qual or havingQual, canonicalize it.
	 */
	if (kind == EXPRKIND_QUAL)
	{
		expr = (Node *) canonicalize_qual((Expr *) expr);

#ifdef OPTIMIZER_DEBUG
		printf("After canonicalize_qual()\n");
		pprint(expr);
#endif
	}

	/* SubLinks to be done */
	if ((root->parse->hasSubLinks) && kind == EXPRKIND_QUAL) {
		//expr = ppg_process_sublinks_in_having(root, expr, true);
	}

	if (kind == EXPRKIND_QUAL)
		expr = (Node *) make_ands_implicit((Expr *) expr);

	return expr;
}

static int
get_grouping_column_index(Query *parse, TargetEntry *tle)
{
        int                     colno = 0;                     
        Index           ressortgroupref = tle->ressortgroupref;
        ListCell   *gl;

        /* No need to search groupClause if TLE hasn't got a sortgroupref */
        if (ressortgroupref == 0)      
                return -1;

        foreach(gl, parse->groupClause)
        {
                SortGroupClause *grpcl = (SortGroupClause *) lfirst(gl);

                if (grpcl->tleSortGroupRef == ressortgroupref)
                        return colno;                  
                colno++;
        }

        return -1;
}

static void
preprocess_groupclause(PlannerInfo *root)
{
        Query      *parse = root->parse;
        List       *new_groupclause;   
        bool            partial_match; 
        ListCell   *sl;
        ListCell   *gl;    

        /* If no ORDER BY, nothing useful to do here */
        if (parse->sortClause == NIL)  
                return;       

        new_groupclause = NIL;
        foreach(sl, parse->sortClause) 
        {
                SortGroupClause *sc = (SortGroupClause *) lfirst(sl);

                foreach(gl, parse->groupClause)
                {
                        SortGroupClause *gc = (SortGroupClause *) lfirst(gl);

                        if (equal(gc, sc))             
                        {
                                new_groupclause = lappend(new_groupclause, gc);
                                break;                         
                        }
                }
                if (gl == NULL)                
                        break;                          /* no match, so stop scanning */
        }

        /* Did we match all of the ORDER BY list, or just some of it? */
        partial_match = (sl != NULL);  

        /* If no match at all, no point in reordering GROUP BY */
        if (new_groupclause == NIL)    
                return;

        foreach(gl, parse->groupClause)
        {
                SortGroupClause *gc = (SortGroupClause *) lfirst(gl);

                if (list_member_ptr(new_groupclause, gc))
                        continue;                       /* it matched an ORDER BY item */
                if (partial_match)
                        return;                         /* give up, no common sort possible */
                if (!OidIsValid(gc->sortop))
                        return;                         /* give up, GROUP BY can't be sorted */
                new_groupclause = lappend(new_groupclause, gc);
        }

        /* Success --- install the rearranged GROUP BY list */
        Assert(list_length(parse->groupClause) == list_length(new_groupclause));
        parse->groupClause = new_groupclause;
}

static List *
make_fullplanTargetList(PlannerInfo *root, List *tlist, AttrNumber **groupColIdx,
                        bool *need_tlist_eval, List** havingTlePosition, List**havingTle)
{
        Query      *parse = root->parse;
        List       *full_tlist;
        List       *non_group_cols;
        int                     numCols;
        int     next_resno ;
        ListCell   *tl;
        *groupColIdx = NULL;

        if (!parse->hasAggs && !parse->groupClause && !root->hasHavingQual &&
			!parse->hasWindowFuncs)
        {
                *need_tlist_eval = true;
                return tlist;
        }

        full_tlist = NIL;
        non_group_cols = NIL;
        *need_tlist_eval = false;       /* only eval if not flat tlist */
	*havingTle = NIL;
	*havingTlePosition = NIL;
        numCols = list_length(parse->groupClause);
        if (numCols > 0)
        {
                AttrNumber *grpColIdx;

                grpColIdx = (AttrNumber *) palloc0(sizeof(AttrNumber) * numCols);
                *groupColIdx = grpColIdx;

                foreach(tl, tlist)
                {
                        TargetEntry *tle = (TargetEntry *) lfirst(tl);
                        int                     colno;

                        colno = get_grouping_column_index(parse, tle);
                        if (colno >= 0)
                        {
                                TargetEntry *newtle;

                                newtle = makeTargetEntry(tle->expr,
                                                                                 list_length(full_tlist) + 1,
                                                                                 tle->resname,
                                                                                 false);
				newtle->ressortgroupref = tle->ressortgroupref;
                                full_tlist = lappend(full_tlist, newtle);

                                Assert(grpColIdx[colno] == 0);  /* no dups expected */
                                grpColIdx[colno] = newtle->resno;

                                if (!(newtle->expr && IsA(newtle->expr, Var)))
                                        *need_tlist_eval = true;        /* tlist contains non Vars */
                        }
                        else
                        {
                                non_group_cols = lappend(non_group_cols, tle);
                        }
                }
        }
        else
        {
                non_group_cols = list_copy(tlist);
        }
        full_tlist = list_concat(full_tlist, non_group_cols);
        non_group_cols = NULL;

        if (parse->havingQual) {
		*havingTle = pull_var_clause((Node *) (parse->havingQual),
                                                                         PVC_INCLUDE_AGGREGATES,
                                                                         PVC_INCLUDE_PLACEHOLDERS);
		non_group_cols = list_copy(*havingTle);
	}

        next_resno = list_length(full_tlist) + 1;

        foreach(tl, non_group_cols)
        {
                Node       *expr = (Node *) lfirst(tl);
                TargetEntry *noGroupTl = tlist_member(expr, full_tlist);
                if (noGroupTl == NULL)
                {
                        TargetEntry *tle;

                        *havingTlePosition = lappend_int(*havingTlePosition, next_resno);
                        tle = makeTargetEntry(copyObject(expr),         /* copy needed?? */
                                                                  next_resno++,
                                                                  NULL,
                                                                  false);
                        full_tlist = lappend(full_tlist, tle);
                } else {
                        *havingTlePosition = lappend_int(*havingTlePosition, noGroupTl->resno);
                }
        }
        /* clean up cruft */
        list_free(non_group_cols);

        return full_tlist;
}

/*
 * locate_grouping_columns
 *		Locate grouping columns in the tlist chosen by create_plan.
 *
 * This is only needed if we don't use the sub_tlist chosen by
 * make_fullplanTargetList.	We have to forget the column indexes found
 * by that routine and re-locate the grouping exprs in the real sub_tlist.
 */
static void
locate_grouping_columns(PlannerInfo *root,
						List *tlist,
						List *sub_tlist,
						AttrNumber *groupColIdx)
{
	int			keyno = 0;
	ListCell   *gl;

	/*
	 * No work unless grouping.
	 */
	if (!root->parse->groupClause)
	{
		Assert(groupColIdx == NULL);
		return;
	}
	Assert(groupColIdx != NULL);

	foreach(gl, root->parse->groupClause)
	{
		SortGroupClause *grpcl = (SortGroupClause *) lfirst(gl);
		Node	   *groupexpr = get_sortgroupclause_expr(grpcl, tlist);
		TargetEntry *te = tlist_member(groupexpr, sub_tlist);

		if (!te)
			elog(ERROR, "failed to locate grouping columns");
		groupColIdx[keyno++] = te->resno;
	}
}

/*
 * preprocess_rowmarks - set up PlanRowMarks if needed
 */
static void
preprocess_rowmarks(PlannerInfo *root)
{
// to be done
}

static TargetEntry *createNewTargetEntry(List *funcname, List *fargs, bool agg_star, bool agg_distinct, bool func_variadic,
		bool resjunk, bool is_column, int location, char*colname, AttrNumber resno)
{
	Oid			rettype;
	Oid			funcid;
	ListCell   *l;
	ListCell   *nextl;
	int			nargs;
	Oid			actual_arg_types[FUNC_MAX_ARGS];
	Oid		   *declared_arg_types;
	List	   *argnames;
	List	   *argdefaults;
	bool		retset;
	int			nvargs;
	FuncDetailCode fdresult;

	/*
	 * Most of the rest of the parser just assumes that functions do not have
	 * more than FUNC_MAX_ARGS parameters.	We have to test here to protect
	 * against array overruns, etc.  Of course, this may not be a function,
	 * but the test doesn't hurt.
	 */
	if (list_length(fargs) > FUNC_MAX_ARGS)
		ereport(ERROR,
				(errcode(ERRCODE_TOO_MANY_ARGUMENTS),
			 errmsg_plural("cannot pass more than %d argument to a function",
						   "cannot pass more than %d arguments to a function",
						   FUNC_MAX_ARGS,
						   FUNC_MAX_ARGS)));

	/*
	 * Extract arg type info in preparation for function lookup.
	 *
	 * If any arguments are Param markers of type VOID, we discard them from
	 * the parameter list.	This is a hack to allow the JDBC driver to not
	 * have to distinguish "input" and "output" parameter symbols while
	 * parsing function-call constructs.  We can't use foreach() because we
	 * may modify the list ...
	 */
	nargs = 0;
	for (l = list_head(fargs); l != NULL; l = nextl)
	{
		Node	   *arg = lfirst(l);
		Oid			argtype = exprType(arg);

		nextl = lnext(l);

		if (argtype == VOIDOID && IsA(arg, Param) &&!is_column)
		{
			fargs = list_delete_ptr(fargs, arg);
			continue;
		}

		actual_arg_types[nargs++] = argtype;
	}

	/*
	 * Check for named arguments; if there are any, build a list of names.
	 *
	 * We allow mixed notation (some named and some not), but only with all
	 * the named parameters after all the unnamed ones.  So the name list
	 * corresponds to the last N actual parameters and we don't need any extra
	 * bookkeeping to match things up.
	 */
	argnames = NIL;
	foreach(l, fargs)
	{
		Node	   *arg = lfirst(l);

		if (IsA(arg, NamedArgExpr))
		{
			NamedArgExpr *na = (NamedArgExpr *) arg;
			ListCell   *lc;

			/* Reject duplicate arg names */
			foreach(lc, argnames)
			{
				if (strcmp(na->name, (char *) lfirst(lc)) == 0)
					ereport(ERROR,
							(errcode(ERRCODE_SYNTAX_ERROR),
						   errmsg("argument name \"%s\" used more than once",
								  na->name)));
			}
			argnames = lappend(argnames, na->name);
		}
		else
		{
			if (argnames != NIL)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
				  errmsg("positional argument cannot follow named argument")));
		}
	}

	fdresult = func_get_detail(funcname, fargs, argnames, nargs,
							   actual_arg_types,
							   !func_variadic, true,
							   &funcid, &rettype, &retset, &nvargs,
							   &declared_arg_types, &argdefaults);
	Assert(fdresult == FUNCDETAIL_AGGREGATE);
	Aggref	*aggref = (Aggref*)makeNode(Aggref);

	aggref->aggfnoid = funcid;
	aggref->aggtype = rettype;
	aggref->aggstar = agg_star;
	aggref->location = location;
	//aggref->args = fargs; //Later to provide the args
	return makeTargetEntry((Expr *)aggref, resno, colname, resjunk);
}
/*
 * create new target list so that we can push down agg to backend nodes
 * */
static void createNewTargetEntryList(TargetListContext *targetListContext, List *targetList)
{
	TargetEntry * tmpTle = NULL;
	TargetEntry *currentTle = NULL;	
	ListCell *tl = NULL;
        Node	* currentExpr = NULL;
	AttrNumber tmpResno = 1;

	foreach(tl, targetList)
	{
		//uptle = NULL;
		if (IsA((Node*)lfirst(tl), TargetEntry)) {
			currentTle = (TargetEntry *)lfirst(tl);
			currentExpr = (Node*)(currentTle->expr);
		} else if (IsA((Node*)lfirst(tl), Var) || IsA((Node*)lfirst(tl), Aggref) ||
			IsA((Node*)lfirst(tl), OpExpr) || IsA((Node*)lfirst(tl), CaseExpr) ||
			IsA((Node*)lfirst(tl), Const) || IsA((Node*)lfirst(tl), FuncExpr)) {
			currentExpr = (Node*)lfirst(tl);
			
			// set resno to be -1, will be fixed later
			currentTle = makeTargetEntry((Expr *)currentExpr,-1, NULL, false);
		} else {
			ereport(ERROR, (errmsg("ppg_fdw does not support this node type ")));
		}

		if (IsA(currentExpr, Aggref)){
			Aggref *aggOld = (Aggref*)(currentExpr);
		    	char * aggname = getFuncName(aggOld->aggfnoid);	
			if(strcmp(aggname,"avg" ) == 0) {
				/* for avg node, we need to rewrite it to be   (/) (OpExpr)
									       / \
									      /   \
                                                                          (sum)   (sum)
									  /           \
                                                                         /             \
                                                                     (sum)            (count)  the nodes on this level will be sent to remote db
				*/
				List* sumArg = NULL;
				ListCell *lc;
				foreach(lc, aggOld->args)
				{
					TargetEntry *aggArgTle = (TargetEntry *)lfirst(lc);
					sumArg = lappend(sumArg, aggArgTle->expr);
				}
				// make the sum node which will be parsed and pusd down to remote database, so just make sure the semantic is right
				List* sum =list_make1(makeString("sum"));
				TargetEntry *targetSum = createNewTargetEntry(sum, sumArg, false, false, false, currentTle->resjunk, false, aggOld->location,
										currentTle->resname, targetListContext->intelResno);
				((Aggref*)(targetSum->expr))->args = (List *) copyObject(((Aggref*)(currentExpr))->args);
				targetListContext->intelResno++;
				targetListContext->deparseList = lappend(targetListContext->deparseList, targetSum);

				// make the count node which will be parsed and pusd down to remote database, so just make sure the semantic is right
				List* count = list_make1(makeString("count"));
				List* cntArg = sumArg;
				TargetEntry *targetCnt = createNewTargetEntry(count, cntArg,false,false,false, currentTle->resjunk, false, aggOld->location, 
										currentTle->resname, targetListContext->intelResno);
				((Aggref*)(targetCnt->expr))->args = (List *) copyObject(((Aggref*)(currentExpr))->args);
				targetListContext->intelResno++;
				targetListContext->deparseList = lappend(targetListContext->deparseList, targetCnt);

				// make the var node to represent the sum node created just now. And this var will be the parameter to sum node uper 
				// so make the uper sum node, this node is the left parameter to "/" op node
				// make sure the resno is right for var node, which need some tricky 
				sumArg = NULL;
				sumArg = lappend(sumArg, (Aggref*)(targetSum->expr));
				TargetEntry *upperLeftSum = createNewTargetEntry(sum, sumArg, false, false, false, currentTle? currentTle->resjunk:false, false, 
										((Aggref*)(targetSum->expr))->location, currentTle?currentTle->resname:NULL, targetSum->resno);
				Var* leftTleVar = makeVar(targetSum->resno, targetSum->resno, ((Aggref*)(targetSum->expr))->aggtype, -1, 
							((Aggref*)(targetSum->expr))->aggcollid, 0);
				TargetEntry * intelLeftTle = (TargetEntry *)makeTargetEntry((Expr*)leftTleVar, targetSum->resno, 
												currentTle->resname, currentTle->resjunk);
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelLeftTle));
				/*since we know just it is count agg, so set the resno to bt 1*/
				intelLeftTle->resno = 1;
				((Aggref*)(upperLeftSum->expr))->args = list_make1(intelLeftTle);

				// make the var node to represent the count node created just now. And this var will be the parameter to sum node uper 
				// so make the uper sum node at the same time, this node is the right parameter to "/" op node
				sumArg = NULL;
				sumArg = lappend(sumArg, (Aggref*)(targetCnt->expr));
				TargetEntry *upperRightSum = createNewTargetEntry(sum, sumArg, false, false, false, targetCnt->resjunk, false, 
										((Aggref*)(targetCnt->expr))->location, targetCnt->resname, targetCnt->resno);

				Var* rightTleVar = makeVar(targetCnt->resno, targetCnt->resno, ((Aggref*)(targetCnt->expr))->aggtype, -1, 
							((Aggref*)(targetCnt->expr))->aggcollid, 0);
				TargetEntry * intelRightTle = (TargetEntry *)makeTargetEntry((Expr*)rightTleVar, targetCnt->resno, currentTle->resname, currentTle->resjunk);
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelRightTle));
				/*since we know just it is sum agg, so set the resno to bt 1*/
				intelRightTle->resno = 1;
				((Aggref*)(upperRightSum->expr))->args = list_make1(intelRightTle);

				// make the "/" operator node, please make sure the parameters is right, and the resno is OK
				List* devide = list_make1(makeString("/"));
				Operator tup = oper(NULL,devide,((Aggref*)(upperLeftSum->expr))->aggtype,((Aggref*)(upperRightSum->expr))->aggtype,false,targetListContext->outerResno);
				Form_pg_operator opform  = (Form_pg_operator) GETSTRUCT(tup);

				OpExpr	   *result = makeNode(OpExpr);
				result->opno = oprid(tup);
				result->opfuncid = opform->oprcode;
				result->opresulttype = opform->oprresult;//rettype;
				result->opretset = get_func_retset(opform->oprcode);
				result->args = list_make2(upperLeftSum->expr, upperRightSum->expr);
				result->location = aggOld->location;

				ReleaseSysCache(tup);
				tmpTle = (TargetEntry *)makeTargetEntry((Expr *)result, targetListContext->outerResno, 
														currentTle->resname, currentTle->resjunk);
				if (currentTle->ressortgroupref > 0) {
					tmpTle->ressortgroupref = currentTle->ressortgroupref ;
				}
				targetListContext->outerList = lappend(targetListContext->outerList,tmpTle);
				targetListContext->outerResno++;
			} else if(strcmp(aggname, "count") == 0 || strcmp(aggname, "sum") == 0) {
				// for count/sum node, we need to rewrite the node as this:
				//			sum
				//                       |
				//                       |
                                //                      sum or count   // push down to remote database
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
				if (tmpTle != NULL) {
					tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);			
					tmpResno = tmpTle->resno;
				} else {
					targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *)copyObject(currentTle));
					tmpResno = targetListContext->intelResno;
					currentTle->resno = targetListContext->intelResno;
					targetListContext->intelResno++;
				}
				Var* tleVar = makeVar(tmpResno, tmpResno, aggOld->aggtype, -1, aggOld->aggcollid, 0);
				tleVar->location = exprLocation((Node*)(currentExpr));
				TargetEntry * intelTle = (TargetEntry *)makeTargetEntry((Expr*)tleVar, tmpResno, currentTle->resname, currentTle->resjunk);
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelTle));
				// just one arg, so set the resno to be 1
				intelTle->resno = 1;
				List* funcname = list_make1(makeString("sum"));
				List* funArg = list_make1(tleVar);
				tmpTle = createNewTargetEntry(funcname, funArg, false, false, false, currentTle->resjunk, false, 
							aggOld->location, currentTle->resname, targetListContext->outerResno);
				((Aggref*)(tmpTle->expr))->args = list_make1(intelTle);
				//s = nodeToString(tmpTle);
				//elog(INFO, "\n output top expr %s\n", pretty_format_node_dump(s));
				if (currentTle->ressortgroupref > 0) {
					tmpTle->ressortgroupref = currentTle->ressortgroupref ;
				}
				targetListContext->outerList = lappend(targetListContext->outerList,	tmpTle);			
				targetListContext->outerResno++;
			} else if(strcmp(aggname, "max") == 0 || strcmp(aggname, "min") == 0){
				// for max and min, we rewrite it as following;
 				//                    max or min
				//                     |
				//                     |
				//                    max or min // push down to remote database 
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
				if (tmpTle != NULL) {
					tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);
					currentTle->resno = targetListContext->outerResno;
					((Var*)currentExpr)->varattno = tmpTle->resno;
					targetListContext->outerList = lappend(targetListContext->outerList, (TargetEntry *)copyObject(currentTle));
				} else {
					targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *) copyObject(currentTle));
					currentTle->resno = targetListContext->intelResno;
					//targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(currentTle));
					TargetEntry * newTle = (TargetEntry *)copyObject(currentTle);
					Var* tleVar = makeVar(targetListContext->intelResno, targetListContext->intelResno, aggOld->aggtype, -1, aggOld->aggcollid, 0);
					tleVar->location = exprLocation((Node*)(currentExpr));
					TargetEntry * intelTle = (TargetEntry *)makeTargetEntry((Expr*)tleVar, targetListContext->intelResno, NULL, currentTle->resjunk);
					targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelTle));
					intelTle->resno = 1;
					((Aggref*)(newTle->expr))->args = list_make1(intelTle);
					newTle->resno = targetListContext->outerResno;
					targetListContext->outerList = lappend(targetListContext->outerList, (TargetEntry *)copyObject(newTle));
					++targetListContext->intelResno;
				}
				targetListContext->outerResno++;
			} else {
				ereport(LOG, (errmsg("unkown name ")));

			}
		} else if (IsA(currentExpr, Var) || IsA(currentExpr, Const)){
			// for var node, is simple, the var node is the same as the var node local, execpt the resno
			tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
			if (tmpTle != NULL) {
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);
				currentTle->resno = targetListContext->outerResno;
				((Var*)currentExpr)->varattno = tmpTle->resno;
			} else {
				currentTle->resno = targetListContext->intelResno;
				targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *) copyObject(currentTle));
				((Var*)currentExpr)->varattno = targetListContext->intelResno;
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(currentTle));
				currentTle->resno = targetListContext->outerResno;
				targetListContext->intelResno++;
			}
			targetListContext->outerList = lappend(targetListContext->outerList, (TargetEntry *) copyObject(currentTle));
			targetListContext->outerResno++;
		} else if (IsA(currentExpr, FuncExpr)) {
			tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
			if (tmpTle != NULL) {
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);
				currentTle->resno = targetListContext->outerResno;
				((Var*)currentExpr)->varattno = tmpTle->resno;
			} else {
				currentTle->resno = targetListContext->intelResno;
				targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *) copyObject(currentTle));
				Var* tleVar = makeVar(targetListContext->intelResno, targetListContext->intelResno, ((FuncExpr*)currentExpr)->funcresulttype,
										-1, ((FuncExpr*)currentExpr)->funccollid, 0);
				tleVar->location = exprLocation((Node*)(currentExpr));
				TargetEntry * intelTle = (TargetEntry *)makeTargetEntry((Expr*)tleVar, targetListContext->intelResno, currentTle->resname, currentTle->resjunk);
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelTle));
				if (currentTle->ressortgroupref > 0) {
					intelTle->ressortgroupref = currentTle->ressortgroupref ;
				}
				currentTle = intelTle;
				targetListContext->intelResno++;
			}
			currentTle->resno = targetListContext->outerResno;
			targetListContext->outerList = lappend(targetListContext->outerList, (TargetEntry *) copyObject(currentTle));
			targetListContext->outerResno++;
		} else if (IsA(currentExpr, OpExpr)) {
			// for operator node, how to rewrite the node depends on whether the parameter is Agg
			// if parameters don't contan Agg, we need to rewrite it as:
			//                                var
			//                                 |
			//                                 |
			//                                 op         op push down to remote database

			// else, the rewriten node is little of complicated
			//				     op
			//                               /        \
			//                              /          \
			//                             op           op         note: op can be a recurse expression 
			//                            / \          /  \       for example: count(a) + sum(b)*avg(c)
                        //                           /   \        /    \       //
                        //                         agg   agg     agg    agg
                        //                       /   \   /  \   /  \    /   \
			//                     agg agg agg agg agg agg agg agg    push down to remote database 
			OpExpr	*opExpr =  (OpExpr*)(currentExpr);
			
			if (!opHasAgg((Node*)opExpr)) { 
				// no agg argument, just create a var
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
				if (tmpTle != NULL) {
					tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);
					currentTle = (TargetEntry *) copyObject(tmpTle);
				} else {
					currentTle->resno = targetListContext->intelResno;
					targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *) copyObject(currentTle));
					Var* tleVar = makeVar(targetListContext->intelResno, targetListContext->intelResno, opExpr->opresulttype, -1, opExpr->opcollid, 0);
					tleVar->location = exprLocation((Node*)(currentExpr));
					TargetEntry * intelTle = (TargetEntry *)makeTargetEntry((Expr*)tleVar, targetListContext->intelResno, currentTle->resname, currentTle->resjunk);
					targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelTle));
					if (currentTle->ressortgroupref > 0) {
						intelTle->ressortgroupref = currentTle->ressortgroupref ;
					}
					currentTle = intelTle;
					targetListContext->intelResno++;
				}
				currentTle->resno = targetListContext->outerResno;
				targetListContext->outerList = lappend(targetListContext->outerList, currentTle);
				targetListContext->outerResno++;
			} else {
				TargetListContext *tmpTargetListContext = (TargetListContext *)palloc0(sizeof(TargetListContext));
				List *operArgs = NULL;
				TargetEntry *tmpLeftTle = NULL;
				TargetEntry *tmpRightTle = NULL;
				char * opName = get_opname(opExpr->opno);
				if (opName == NULL) {
					ereport(ERROR, (errmsg("Failed to get the operator name")));
				}
				List* opNameStr = list_make1(makeString(opName));
				tmpTargetListContext->deparseList = targetListContext->deparseList;
				tmpTargetListContext->intelList = targetListContext->intelList;

				tmpTargetListContext->intelResno = targetListContext->intelResno;
				tmpTargetListContext->outerResno = targetListContext->intelResno;
				createNewTargetEntryList(tmpTargetListContext, opExpr->args);	
				targetListContext->deparseList = tmpTargetListContext->deparseList;
				targetListContext->intelList = tmpTargetListContext->intelList;
				targetListContext->intelResno = tmpTargetListContext->outerResno;
				if (length(tmpTargetListContext->outerList)==1) {
					ListCell *tmpLeftCell = list_head(tmpTargetListContext->outerList);
					tmpLeftTle = (TargetEntry *)lfirst(tmpLeftCell);
					operArgs = list_make1((Expr *) copyObject(tmpLeftTle->expr));

				} else if (length(tmpTargetListContext->outerList)==2) {
					ListCell *tmpLeftCell = list_head(tmpTargetListContext->outerList);
					tmpLeftTle = (TargetEntry *)lfirst(tmpLeftCell);
					ListCell *tmpRightCell = lnext(tmpLeftCell);
					tmpRightTle = (TargetEntry *)lfirst(tmpRightCell);
					operArgs = list_make2((Expr *) copyObject(tmpLeftTle->expr),
								(Expr *) copyObject(tmpRightTle->expr));
				} else {
					ereport(ERROR, (errmsg("the number of args should be 1 or 2")));
				}
				Operator tup = oper(NULL,opNameStr,exprType((Node*)(tmpLeftTle->expr)),
							tmpRightTle ? exprType((Node*)(tmpRightTle->expr)) : InvalidOid,
							false,targetListContext->outerResno);
				Form_pg_operator opform  = (Form_pg_operator) GETSTRUCT(tup);

				OpExpr	   *result = makeNode(OpExpr);
				result->opno = oprid(tup);
				result->opfuncid = opform->oprcode;
				result->opresulttype = opform->oprresult;//rettype;
				result->opretset = get_func_retset(opform->oprcode);
				result->args = operArgs;
				result->location = targetListContext->outerResno;
				tmpTle = (TargetEntry *)makeTargetEntry((Expr *)result, targetListContext->outerResno, 
														currentTle->resname, currentTle->resjunk);
				if (currentTle->ressortgroupref > 0) {
					tmpTle->ressortgroupref = currentTle->ressortgroupref ;
				}

				ReleaseSysCache(tup);
				targetListContext->outerList = lappend(targetListContext->outerList, tmpTle);
				targetListContext->outerResno++;
			}
		} else if (IsA(currentExpr, CaseExpr)) {
			// for CaseExpr, we need to rewrite it as:
			//                                var
			//                                 |
			//                                 |
			//                              CaseExpr        // CaseExpr push down to remote database
			CaseExpr	*caseExpr =  (CaseExpr*)(currentExpr);
			tmpTle = tlist_member((Node*)(currentExpr), targetListContext->deparseList);
			if (tmpTle != NULL) {
				tmpTle = tlist_member((Node*)(currentExpr), targetListContext->intelList);
				currentTle = (TargetEntry *) copyObject(tmpTle);
			} else {
				currentTle->resno = targetListContext->intelResno;
				targetListContext->deparseList = lappend(targetListContext->deparseList, (TargetEntry *) copyObject(currentTle));
				Var* tleVar = makeVar(targetListContext->intelResno, targetListContext->intelResno, caseExpr->casetype, -1, caseExpr->casecollid, 0);
				tleVar->location = exprLocation((Node*)(currentExpr));
				TargetEntry * intelTle = (TargetEntry *)makeTargetEntry((Expr*)tleVar, targetListContext->intelResno, currentTle->resname, currentTle->resjunk);
				targetListContext->intelList = lappend(targetListContext->intelList, (TargetEntry *) copyObject(intelTle));
				if (currentTle->ressortgroupref > 0) {
					intelTle->ressortgroupref = currentTle->ressortgroupref ;
				}
				currentTle = intelTle;
				targetListContext->intelResno++;
			}
			currentTle->resno = targetListContext->outerResno;
			targetListContext->outerList = lappend(targetListContext->outerList, currentTle);
			targetListContext->outerResno++;

		} else {
			ereport(ERROR, (errmsg("does not support this node type ")));
		}
	}
}

static bool opHasAgg (Node *node)
{
	bool result = false;
	Assert( IsA(node, OpExpr));
	OpExpr	*opExpr =  (OpExpr*)(node);
	ListCell *tmpCell;
	foreach (tmpCell, opExpr->args) {
		if (IsA((Node*)lfirst(tmpCell), Aggref)) {
			result = true;
		} else if (IsA((Node*)lfirst(tmpCell), OpExpr)) {
			result = opHasAgg((Node*)lfirst(tmpCell));
		}
		if (result) {
			break;
		}
	}
	return result;
}

static int32 getTlistWidth(List *outerTleList)
{
	ListCell   *lc;
	int32       item_width = 0;
	int32       tmp = 0;
	foreach(lc, outerTleList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);
		tmp= get_typavgwidth(exprType(tle->expr), exprTypmod(tle->expr));
		if (tmp == 32){
			item_width += 4;
		} else {
			item_width += tmp;
		}
	}
	return item_width;
}

static List *handleSubquery (PlannerInfo *root)
{
        List            *subplanList = NULL;
        ListCell        *lc; 
        Query *parse = root->parse;
        SubPlanPath  planPath;
        planPath.root = root;
        planPath.source = NULL;
        planPath.planID = 0; 
        planPath.subPlanList = NULL;
        planPath.outRows = 0; 
        planPath.rowSize = 0; 
        getSubPlanPath(parse, &planPath);
        foreach (lc, planPath.subPlanList)
        {    
                SubPlanPath  *subPath = lfirst(lc);
                SubQueryPlan* subplan = (SubQueryPlan*)palloc(sizeof(SubQueryPlan));
                createSubplan(subplan, subPath->source);
                subplan->subplanIndex = subPath->planID;
                subplan->dmethod = All; 
                subplanList = lappend(subplanList,subplan);
        }    

        if (length(parse->jointree->fromlist) == 1 && length(subplanList) == 1) { 
                Node *fromNode = lfirst(list_head(parse->jointree->fromlist));
                if (IsA(fromNode, RangeTblRef)) {
                        int varno = ((RangeTblRef *) fromNode)->rtindex;
                        RangeTblEntry *fromRte = rt_fetch(varno, parse->rtable);
                        Node *srcNode = ((SubPlanPath  *)lfirst(list_head(planPath.subPlanList)))->source;
            if (equal(fromRte, srcNode)) {     
                ListCell        *lc1;     
                    forboth (lc, subplanList, lc1, planPath.subPlanList)
                                {     
                        SubPlanPath  *subPath = lfirst(lc1);
                    if (subPath->type == InFrom) {
                                                SubQueryPlan* subplan = lfirst(lc);
                                                subplan->dmethod = RoundRobin;
                                        }    
                                }     
                }    
                }     
        }    
        return subplanList;
}

// It will be called when subquery exsits 
static void rewriteOrignalTargetList (PlannerInfo *root) 
{
        Query *parse = root->parse;
        ListCell        *lc; 
        RewriteOrignalTargetContext context;
        context.parse = parse;
        context.currentExpr = NULL;
        foreach(lc, parse->targetList) {
                TargetEntry *curTe = lfirst(lc);
                context.currentExpr = curTe->expr;
                context.changed = false;
                rewriteOrignalTargetListWalker(&context);
        }
}

static void rewriteOrignalTargetListWalker (RewriteOrignalTargetContext *context)
{
        Node *currentExpr = context->currentExpr;
        if (IsA(currentExpr, Aggref)){
                ListCell *lc;
                bool argChanged = false;
                Aggref *aggOld = (Aggref*)(currentExpr);
                if (aggOld->aggstar) {
                        context->changed = false;
                        return;
                }
                foreach(lc, aggOld->args)
                {
                        TargetEntry *aggArgTle = (TargetEntry *)lfirst(lc);
                        context->currentExpr = aggArgTle->expr;
                        context->changed = false;
                        rewriteOrignalTargetListWalker(context);
                        argChanged |= context->changed;
                }
                if (argChanged) {
                        char * aggname = getFuncName(aggOld->aggfnoid);
                        if(!(strcmp(aggname,"avg" ) == 0 || strcmp(aggname, "count") == 0 || strcmp(aggname, "sum") == 0)
                                || (strcmp(aggname, "max") == 0 || strcmp(aggname, "min") == 0)) {
                                ereport(ERROR, (errmsg("unkown name ")));
                        }
                        List* aggNameList =list_make1(makeString(aggname));
                        TargetEntry *newTarget = createNewTargetEntry(aggNameList, aggOld->args, false, false, false, true, false, -1,
                                                                NULL, 1);
                        aggOld->aggfnoid = ((Aggref*)(newTarget->expr))->aggfnoid;
                        aggOld->aggtype = ((Aggref*)(newTarget->expr))->aggtype;
                        aggOld->aggcollid = ((Aggref*)(newTarget->expr))->aggcollid;
                        // save the changed
                        context->currentExpr = argChanged;
                }
                // restore the orignal expr
                context->currentExpr = currentExpr;
        } else if (IsA(currentExpr, Var)){
                Var     *varExpr = (Var*)(currentExpr);
                int varno = varExpr->varno;
                RangeTblEntry *rte = rt_fetch(varno, context->parse->rtable);
                if (rte->rtekind == RTE_SUBQUERY) {
                        Query* subquery = rte->subquery;
                        TargetEntry *referencedTe = list_nth(subquery->targetList, varExpr->varattno-1);
                        varExpr->vartype = exprType(((Node*)(referencedTe->expr)));
                        varExpr->vartypmod = exprTypmod(((Node*)(referencedTe->expr)));
                        context->changed = true;
                }
        } else if( IsA(currentExpr, Const)){
                context->changed = false;
                return;
      } else if (IsA(currentExpr, FuncExpr)) {
                context->changed = false;
                return;
        } else if (IsA(currentExpr, OpExpr)) {
                OpExpr  *opExpr =  (OpExpr*)(currentExpr);
                ListCell *lc;
                bool argChanged = false;
                foreach(lc, opExpr->args)
                {
                        TargetEntry *opArgTle = (TargetEntry *)lfirst(lc);
                        context->currentExpr = opArgTle->expr;
                        context->changed = false;
                        rewriteOrignalTargetListWalker(context);
                        argChanged |= context->changed;
                }
                if (argChanged) {
                        TargetEntry *tmpLeftTle = NULL;
                        TargetEntry *tmpRightTle = NULL;
                        char * opName = get_opname(opExpr->opno);
                        if (opName == NULL) {
                                ereport(ERROR, (errmsg("Failed to get the operator name")));
                        }
                        List* opNameStr = list_make1(makeString(opName));
                        if (length(opExpr->args)==1) {
                                ListCell *tmpLeftCell = list_head(opExpr->args);
                                tmpLeftTle = (TargetEntry *)lfirst(tmpLeftCell);
                        } else if (length(opExpr->args)==2) {
                                ListCell *tmpLeftCell = list_head(opExpr->args);
                                tmpLeftTle = (TargetEntry *)lfirst(tmpLeftCell);
                                ListCell *tmpRightCell = lnext(tmpLeftCell);
                                tmpRightTle = (TargetEntry *)lfirst(tmpRightCell);
                        } else {
                                ereport(ERROR, (errmsg("the number of args should be 1 or 2")));
                        }
                        Operator tup = oper(NULL,opNameStr,exprType((Node*)(tmpLeftTle->expr)),
                                                tmpRightTle ? exprType((Node*)(tmpRightTle->expr)) : InvalidOid,
                                                false, 1);
                        Form_pg_operator opform  = (Form_pg_operator) GETSTRUCT(tup);
                        opExpr->opno = oprid(tup);
                        opExpr->opfuncid = opform->oprcode;
                        opExpr->opresulttype = opform->oprresult;//rettype;
                        opExpr->opretset = get_func_retset(opform->oprcode);
                        ReleaseSysCache(tup);
                        // save the changed
                        context->currentExpr = argChanged;
                }
                // restore the orignal expr
                context->currentExpr = currentExpr;

        } else if (IsA(currentExpr, CaseExpr)) {
        } else {
                ereport(ERROR, (errmsg("does not support this node type ")));
        }
        return;
}

static ForeignScan *deparsePlan(PlannerInfo *root, List* subplanList)
{
        List       *fdw_private;
        StringInfoData sql;
        initStringInfo(&sql);
        deparseSelectSql(&sql, root, NULL, NULL);
        fdw_private = list_make3(makeString(sql.data), root->parse->targetList, subplanList);
        return make_foreignscan(NULL, NULL, 0, NULL, fdw_private);
}

static void postProcessSortList(List *sortList, List *newTlist)
{
        ListCell   *l;
        Oid     sortop;
        Oid     eqop;
        bool    hashable;
        foreach(l, sortList)
        {
                SortGroupClause *sortcl = (SortGroupClause *) lfirst(l);
                Expr *sortkey = (Expr *) get_sortgroupclause_expr(sortcl, newTlist);
                Assert(OidIsValid(sortcl->sortop));
                if (sortcl->nulls_first) {
                        // for order asc 
                        get_sort_group_operators(exprType(sortkey), false, true, true,
                                                NULL, &eqop, &sortop, &hashable);
                } else {
                        get_sort_group_operators(exprType(sortkey), true, true, false,
                                                &sortop, &eqop, NULL, &hashable);
                }
                sortcl->eqop = eqop;
                sortcl->sortop = sortop;
                sortcl->hashable = hashable;
        }
        return ;
}

// since we modify the targetlist, we need to modify the SortGroupClause
static void updateSortGroupClause (Query *parse, List *newTlist)
{
        if (parse->groupClause != NIL) {
                postProcessSortList(parse->groupClause, newTlist);
        }
        if (parse->sortClause != NIL) {
                postProcessSortList(parse->sortClause, newTlist);
        }
        if (parse->distinctClause != NIL) {
                postProcessSortList(parse->distinctClause, newTlist);
        }
        return;
}

static Plan *
ppg_grouping_planner(PlannerInfo *root, double tuple_fraction)
{
	Query	   *parse = root->parse;
	List	   *tlist = parse->targetList;
	int64		offset_est = 0;
	int64		count_est = 0;
	double		limit_tuples = -1.0;
	Plan	   *result_plan;
	List	   *current_pathkeys = NIL;
	double		dNumGroups = 0;
	bool		use_hashed_distinct = false;

	/* Tweak caller-supplied tuple_fraction if have LIMIT/OFFSET */
	if (parse->limitCount || parse->limitOffset)
	{
		/*tuple_fraction = preprocess_limit(root, tuple_fraction,
										  &offset_est, &count_est);
*/
		/*
		 * If we have a known LIMIT, and don't have an unknown OFFSET, we can
		 * estimate the effects of using a bounded sort.
		 */
		if (count_est > 0 && offset_est >= 0)
			limit_tuples = (double) count_est + (double) offset_est;
	}

	if (parse->setOperations)
	{
		// To be done
		return NULL;
	}
	else
	{
		/* No set operations, do regular planning */
		List	   *full_tlist = NIL;
		List	   *final_tlist = NIL;
		List	   *havingTleList = NIL;
		List       *havingTlePosition = NIL;
		List       *subplanList = NIL;
		int 		orignalTlistLength = 0;
		double		sub_limit_tuples = 0.0;
		AttrNumber *groupColIdx = NULL;
		bool		need_tlist_eval = true;
		long		numGroups = 0;
		AggClauseCosts agg_costs;
		int			numGroupCols;
		double		path_rows;
		int			path_width;
		bool		use_hashed_grouping = false;
		// handle subquery first 
                subplanList = handleSubquery(root);
                if (subplanList) {
                        rewriteOrignalTargetList(root); 
                }    
		orignalTlistLength = length(tlist);
		MemSet(&agg_costs, 0, sizeof(AggClauseCosts));
		/* A recursive query should always have setOperations */
		Assert(!root->hasRecursion);
		/* Preprocess GROUP BY clause, needed */
		if (parse->groupClause)
			preprocess_groupclause(root);
		numGroupCols = list_length(parse->groupClause);
		/* Preprocess targetlist, needed */
		tlist = preprocess_targetlist(root, tlist);


		/** Gather the full target list from parse tree*/
		full_tlist = make_fullplanTargetList(root, tlist, &groupColIdx, &need_tlist_eval, &havingTlePosition, &havingTleList);

		/*
		 * Generate appropriate target list for subplan; may be different from
		 * tlist if grouping or aggregation is needed.
		 */
		TargetListContext *targetListContext = (TargetListContext *)palloc0(sizeof(TargetListContext));
		targetListContext->intelResno = 1;
		targetListContext->outerResno = 1;
		createNewTargetEntryList(targetListContext, full_tlist);
		parse->targetList = targetListContext->deparseList;
		result_plan = (Plan*)deparsePlan(root, subplanList);

		/* Get the final target list from the revised target list */
		if(orignalTlistLength > 0) {
			ListCell *lc;
			int i = 0;
			foreach (lc, targetListContext->outerList) {
				final_tlist = lappend(final_tlist, (TargetEntry *) lfirst(lc));
				i++;
				if (i == orignalTlistLength) {
					break;
				}
			}
		} else {
			elog(ERROR, "Found no target list \n");
		}
		
		/* create the pathkeys for group, sort and distinct opeations */
		tlist = final_tlist;
		updateSortGroupClause(parse, targetListContext->outerList);
		root->group_pathkeys = NIL;
		if (parse->groupClause && grouping_is_sortable(parse->groupClause)) {
        		root->group_pathkeys =	make_pathkeys_for_sortclauses(root, parse->groupClause, tlist);
		} 	
    		/* We do not consider  window functions now */
        	root->window_pathkeys = NIL;   					
    		if (parse->distinctClause && grouping_is_sortable(parse->distinctClause)) {
        		root->distinct_pathkeys = make_pathkeys_for_sortclauses(root, parse->distinctClause, tlist);                        
		}
 		root->sort_pathkeys = make_pathkeys_for_sortclauses(root, parse->sortClause, tlist);

		result_plan->plan_rows = 100; 
 		result_plan->targetlist = targetListContext->intelList;
		result_plan->plan_width = getTlistWidth(targetListContext->intelList);
		tlist = targetListContext->outerList;
		
		if (root->group_pathkeys) {
			current_pathkeys = root->group_pathkeys;
		} else if (list_length(root->distinct_pathkeys) >  list_length(root->sort_pathkeys)) {
			current_pathkeys = root->distinct_pathkeys;
		}  else if (root->sort_pathkeys) {
			current_pathkeys = root->sort_pathkeys;
		}
	
		if (parse->hasAggs)
		{				
			count_agg_clauses(root, (Node *) tlist, &agg_costs);
			count_agg_clauses(root, parse->havingQual, &agg_costs);
			preprocess_minmax_aggregates(root, tlist);
		}

		if (parse->groupClause || parse->distinctClause || parse->hasAggs ||
			parse->hasWindowFuncs || root->hasHavingQual) {
			sub_limit_tuples = -1.0;
		} else {
			sub_limit_tuples = limit_tuples;

		}
		path_rows = 1;// estimate the resutls set from remote database, to be done		
		path_width = getTlistWidth(tlist);	

		bool	need_sort_for_grouping = false;

		if (parse->groupClause && 
			!pathkeys_contained_in(root->group_pathkeys, current_pathkeys)) {
			need_sort_for_grouping = true;
			need_tlist_eval = true;
		} else if (parse->groupClause) {
			use_hashed_grouping = true;
		}
		if (need_tlist_eval){
			if (!is_projection_capable_plan(result_plan) && !tlist_same_exprs(full_tlist, result_plan->targetlist)) {
				result_plan = (Plan *) make_result(root, full_tlist, NULL, result_plan);
			} else {
				//result_plan->targetlist = full_tlist;
			}
			add_tlist_costs_to_plan(root, result_plan, full_tlist);
		} else {
			locate_grouping_columns(root, tlist, result_plan->targetlist,
										groupColIdx);
		}
		if (root->hasHavingQual) {
                        havingAggContext havingContext;
                        ListCell        *lc1;
                        ListCell        *lc2;
                        havingContext.action = Extract;
                        havingContext.oldAgg = NULL;
                        havingContext.newAgg = NULL;
                        forboth (lc1, havingTleList, lc2, havingTlePosition) {
                                havingContext.oldAgg = (Node *) lfirst(lc1);
                                TargetEntry *newTe = list_nth (targetListContext->outerList, lfirst_int(lc2)-1) ;
                                havingContext.newAgg = newTe->expr;
                                havingContext.action = Replace;
                                handleAggExprInHaving(parse->havingQual, &havingContext);
			}
		}

		if (use_hashed_grouping) {
			result_plan = (Plan *) make_agg(root,
												final_tlist,
												(List *) parse->havingQual,
												AGG_HASHED,
												&agg_costs,
												numGroupCols,
												groupColIdx,
									extract_grouping_ops(parse->groupClause),
												numGroups,
												result_plan);
			current_pathkeys = NIL;
		} else if (parse->hasAggs) {
			AggStrategy aggstrategy;
			if (parse->groupClause) {
				if (need_sort_for_grouping) {
					result_plan = (Plan *) make_sort_from_groupcols(root, parse->groupClause, groupColIdx, result_plan);
					current_pathkeys = root->group_pathkeys;
				}
				aggstrategy = AGG_SORTED;
			} else {
				aggstrategy = AGG_PLAIN;
				current_pathkeys = NIL;
			}

			result_plan = (Plan *) make_agg(root,
												final_tlist,
												(List *) parse->havingQual,
												aggstrategy,
												&agg_costs,
												numGroupCols,
												groupColIdx,
									extract_grouping_ops(parse->groupClause),
												numGroups,
												result_plan);
		} else if (parse->groupClause) {
			if (need_sort_for_grouping) {
				result_plan = (Plan *)
					make_sort_from_groupcols(root,
												 parse->groupClause,
												 groupColIdx,
												 result_plan);
				current_pathkeys = root->group_pathkeys;
			}

			result_plan = (Plan *) make_group(root,
												  final_tlist,
												  (List *) parse->havingQual,
												  numGroupCols,
												  groupColIdx,
									extract_grouping_ops(parse->groupClause),
												  dNumGroups,
												  result_plan);
		} 
	}

	if (parse->distinctClause)
	{
		double		dNumDistinctRows;
		long		numDistinctRows;

		if (parse->groupClause || root->hasHavingQual || parse->hasAggs)
			dNumDistinctRows = result_plan->plan_rows;
		else
			dNumDistinctRows = dNumGroups;

		numDistinctRows = (long) Min(dNumDistinctRows, (double) LONG_MAX);

		use_hashed_distinct = true; // get the right value for this var, to be done
		if (use_hashed_distinct)
		{
			result_plan = (Plan *) make_agg(root,
											result_plan->targetlist,
											NIL,
											AGG_HASHED,
											NULL,
										  list_length(parse->distinctClause),
								 extract_grouping_cols(parse->distinctClause,
													result_plan->targetlist),
								 extract_grouping_ops(parse->distinctClause),
											numDistinctRows,
											result_plan);
			current_pathkeys = NIL;
		}
		else
		{
			List	   *needed_pathkeys;

			if (parse->hasDistinctOn &&
				list_length(root->distinct_pathkeys) <
				list_length(root->sort_pathkeys))
				needed_pathkeys = root->sort_pathkeys;
			else
				needed_pathkeys = root->distinct_pathkeys;

			if (!pathkeys_contained_in(needed_pathkeys, current_pathkeys))
			{
				if (list_length(root->distinct_pathkeys) >=
					list_length(root->sort_pathkeys))
					current_pathkeys = root->distinct_pathkeys;
				else
				{
					current_pathkeys = root->sort_pathkeys;
					/* Assert checks that parser didn't mess up... */
					Assert(pathkeys_contained_in(root->distinct_pathkeys,
												 current_pathkeys));
				}

				result_plan = (Plan *) make_sort_from_pathkeys(root,
															   result_plan,
															current_pathkeys,
															   -1.0);
			}

			result_plan = (Plan *) make_unique(result_plan,
											   parse->distinctClause);
			result_plan->plan_rows = dNumDistinctRows;
		}
	}

	if (parse->sortClause)
	{
		result_plan = (Plan *) make_sort_from_pathkeys(root,
														   result_plan,
														 root->sort_pathkeys,
														   limit_tuples);
		current_pathkeys = root->sort_pathkeys;
	}

	if (limit_needed(parse)) {
		result_plan = (Plan *) make_limit(result_plan,
										  parse->limitOffset,
										  parse->limitCount,
										  offset_est,
										  count_est);
	}

	root->query_pathkeys = current_pathkeys;

	return result_plan;
}

Plan *ppg_subquery_planner(PlannerGlobal *glob, Query *parse,
				 PlannerInfo *parent_root,
				 bool hasRecursion, double tuple_fraction,
				 PlannerInfo **subroot)
{
	int			num_old_subplans = list_length(glob->subplans);
	PlannerInfo *root;
	Plan	   *plan;
	List	   *newHaving;
	ListCell   *l;
	/* Create a PlannerInfo data structure for this subquery */
	root = makeNode(PlannerInfo);
	root->parse = parse;
	root->glob = glob;
	root->query_level = parent_root ? parent_root->query_level + 1 : 1;
	root->parent_root = parent_root;
	root->plan_params = NIL;
	root->planner_cxt = CurrentMemoryContext;
	root->init_plans = NIL;
	root->cte_plan_ids = NIL;
	root->eq_classes = NIL;
	root->append_rel_list = NIL;
	root->rowMarks = NIL;
	root->hasInheritedTarget = false;

	root->hasRecursion = hasRecursion;
	if (hasRecursion)
		root->wt_param_id = SS_assign_special_param(root);
	else
		root->wt_param_id = -1;
	root->non_recursive_plan = NULL;
	/*
	 * If there is a WITH list, process each WITH query and build an initplan
	 * SubPlan structure for it.
	 */
	// NOTE: Dose not support WITH list currently, TBD
	//if (parse->cteList)
	//	SS_process_ctes(root);

	/*
	 * Look for ANY and EXISTS SubLinks in WHERE and JOIN/ON clauses, and try
	 * to transform them into joins.  Note that this step does not descend
	 * into subqueries; if we pull up any subqueries below, their SubLinks are
	 * processed just before pulling them up.
	 */
	if (parse->hasSubLinks)
		pull_up_sublinks(root);

	/*
	 * Scan the rangetable for set-returning functions, and inline them if
	 * possible (producing subqueries that might get pulled up next).
	 * Recursion issues here are handled in the same way as for SubLinks.
	 */
	inline_set_returning_functions(root);

	/*
	 * Check to see if any subqueries in the jointree can be merged into this
	 * query.
	 */
	parse->jointree = (FromExpr *)
		pull_up_subqueries(root, (Node *) parse->jointree);
	//char *s = nodeToString(parse);
	//elog(INFO, "\n after rewriten parse tree  %s\n", pretty_format_node_dump(s));
	//return NULL;
	/*
	 * If this is a simple UNION ALL query, flatten it into an appendrel. We
	 * do this now because it requires applying pull_up_subqueries to the leaf
	 * queries of the UNION ALL, which weren't touched above because they
	 * weren't referenced by the jointree (they will be after we do this).
	 */
	// NOTE: Dose not support union, TBD
	//if (parse->setOperations)
	//	flatten_simple_union_all(root);

	/*
	 * Detect whether any rangetable entries are RTE_JOIN kind; if not, we can
	 * avoid the expense of doing flatten_join_alias_vars().  Also check for
	 * outer joins --- if none, we can skip reduce_outer_joins().  And check
	 * for LATERAL RTEs, too.  This must be done after we have done
	 * pull_up_subqueries(), of course.
	 */
	root->hasJoinRTEs = false;
	root->hasLateralRTEs = false;
	foreach(l, parse->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(l);
		if (rte->lateral)
			root->hasLateralRTEs = true;
	}

	/*
	 * Preprocess RowMark information.	We need to do this after subquery
	 * pullup (so that all non-inherited RTEs are present) and before
	 * inheritance expansion (so that the info is available for
	 * expand_inherited_tables to examine and modify).
	 */
	preprocess_rowmarks(root);

	/*
	 * Expand any rangetable entries that are inheritance sets into "append
	 * relations".  This can add entries to the rangetable, but they must be
	 * plain base relations not joins, so it's OK (and marginally more
	 * efficient) to do it after checking for join RTEs.  We must do it after
	 * pulling up subqueries, else we'd fail to handle inherited tables in
	 * subqueries.
	 */
	expand_inherited_tables(root);

	/*
	 * Set hasHavingQual to remember if HAVING clause is present.  Needed
	 * because preprocess_expression will reduce a constant-true condition to
	 * an empty qual list ... but "HAVING TRUE" is not a semantic no-op.
	 */
	root->hasHavingQual = (parse->havingQual != NULL);

	/* Clear this flag; might get set in distribute_qual_to_rels */
	root->hasPseudoConstantQuals = false;

	/*
	 * Do expression preprocessing on targetlist and quals, as well as other
	 * random expressions in the querytree.  Note that we do not need to
	 * handle sort/group expressions explicitly, because they are actually
	 * part of the targetlist.
	 */
	parse->targetList = (List *)
		preprocess_expression(root, (Node *) parse->targetList,
							  EXPRKIND_TARGET);

	parse->returningList = (List *)
		preprocess_expression(root, (Node *) parse->returningList,
							  EXPRKIND_TARGET);

	preprocess_qual_conditions(root, (Node *) parse->jointree);
	parse->havingQual = ppg_process_sublink_in_having(root, parse->havingQual, true);

	parse->havingQual = preprocess_expression(root, parse->havingQual,
											  EXPRKIND_QUAL);

	foreach(l, parse->windowClause)
	{
		WindowClause *wc = (WindowClause *) lfirst(l);

		/* partitionClause/orderClause are sort/group expressions */
		wc->startOffset = preprocess_expression(root, wc->startOffset,
												EXPRKIND_LIMIT);
		wc->endOffset = preprocess_expression(root, wc->endOffset,
											  EXPRKIND_LIMIT);
	}

	parse->limitOffset = preprocess_expression(root, parse->limitOffset,
											   EXPRKIND_LIMIT);
	parse->limitCount = preprocess_expression(root, parse->limitCount,
											  EXPRKIND_LIMIT);

	root->append_rel_list = (List *)
		preprocess_expression(root, (Node *) root->append_rel_list,
							  EXPRKIND_APPINFO);

	/* Also need to preprocess expressions within RTEs */
	foreach(l, parse->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(l);
		int			kind;

		if (rte->rtekind == RTE_SUBQUERY)
		{
			/*
			 * We don't want to do all preprocessing yet on the subquery's
			 * expressions, since that will happen when we plan it.  But if it
			 * contains any join aliases of our level, those have to get
			 * expanded now, because planning of the subquery won't do it.
			 * That's only possible if the subquery is LATERAL.
			 */
			if (rte->lateral && root->hasJoinRTEs)
				rte->subquery = (Query *)
					flatten_join_alias_vars(root, (Node *) rte->subquery);
		}
		else if (rte->rtekind == RTE_FUNCTION)
		{
			/* Preprocess the function expression fully */
			kind = rte->lateral ? EXPRKIND_RTFUNC_LATERAL : EXPRKIND_RTFUNC;
			rte->funcexpr = preprocess_expression(root, rte->funcexpr, kind);
		}
		else if (rte->rtekind == RTE_VALUES)
		{
			/* Preprocess the values lists fully */
			kind = rte->lateral ? EXPRKIND_VALUES_LATERAL : EXPRKIND_VALUES;
			rte->values_lists = (List *)
				preprocess_expression(root, (Node *) rte->values_lists, kind);
		}
	}

	newHaving = NIL;
	foreach(l, (List *) parse->havingQual)
	{
		Node	   *havingclause = (Node *) lfirst(l);

		if (contain_agg_clause(havingclause) ||
			contain_volatile_functions(havingclause) ||
			contain_subplans(havingclause))
		{
			/* keep it in HAVING */
			newHaving = lappend(newHaving, havingclause);
		}
		else if (parse->groupClause)
		{
			/* move it to WHERE */
			parse->jointree->quals = (Node *)
				lappend((List *) parse->jointree->quals, havingclause);
		}
		else
		{
			/* put a copy in WHERE, keep it in HAVING */
			parse->jointree->quals = (Node *)
				lappend((List *) parse->jointree->quals,
						copyObject(havingclause));
			newHaving = lappend(newHaving, havingclause);
		}
	}
	parse->havingQual = (Node *) newHaving;


	/*
	 * Do the main planning.  If we have an inherited target relation, that
	 * needs special processing, else go straight to grouping_planner.
	 */
	if (parse->resultRelation &&
		rt_fetch(parse->resultRelation, parse->rtable)->inh){
		ereport(ERROR, (errmsg("Does not support  inherited table")));
		return NULL;
		//plan =inheritance_planner(root);
	}
	else
	{
		plan = ppg_grouping_planner(root, tuple_fraction);
		/* If it's not SELECT, we need a ModifyTable node */
		if (parse->commandType != CMD_SELECT)
		{
			List	   *returningLists;
			List	   *rowMarks;

			/*
			 * Set up the RETURNING list-of-lists, if needed.
			 */
			if (parse->returningList)
				returningLists = list_make1(parse->returningList);
			else
				returningLists = NIL;

			/*
			 * If there was a FOR [KEY] UPDATE/SHARE clause, the LockRows node will
			 * have dealt with fetching non-locked marked rows, else we need
			 * to have ModifyTable do that.
			 */
			if (parse->rowMarks)
				rowMarks = NIL;
			else
				rowMarks = root->rowMarks;

			plan = (Plan *) make_modifytable(root,
											 parse->commandType,
											 parse->canSetTag,
									   list_make1_int(parse->resultRelation),
											 list_make1(plan),
											 returningLists,
											 rowMarks,
											 SS_assign_special_param(root));
		}
	}

	/*
	 * If any subplans were generated, or if there are any parameters to worry
	 * about, build initPlan list and extParam/allParam sets for plan nodes,
	 * and attach the initPlans to the top plan node.
	 */
	if (list_length(glob->subplans) != num_old_subplans ||
		root->glob->nParamExec > 0)
		SS_finalize_plan(root, plan, true);

	/* Return internal info if caller wants it */
	if (subroot)
		*subroot = root;

	return plan;
}

static PlannedStmt* ppg_planner(Query *parse, int cursorOptions, ParamListInfo boundParams) {
	PlannedStmt *result;
	PlannerGlobal *glob;
	double		tuple_fraction;
	PlannerInfo *root;
	Plan	   *top_plan;
	RangeTblEntry * finalrtable;
	bool canpush = canAllPush(parse, FDW_handler);

	ereport(LOG,(errmsg("ppg_planner works haha ")));
	if ( !canpush ) {
		return standard_planner(parse,cursorOptions, boundParams);
	}
	/* Cursor options may come from caller or from DECLARE CURSOR stmt */
	if (parse->utilityStmt &&
		IsA(parse->utilityStmt, DeclareCursorStmt))
		cursorOptions |= ((DeclareCursorStmt *) parse->utilityStmt)->options;

	/*
	 * Set up global state for this planner invocation.  This data is needed
	 * across all levels of sub-Query that might exist in the given command,
	 * so we keep it in a separate struct that's linked to by each per-Query
	 * PlannerInfo.
	 */
	glob = makeNode(PlannerGlobal);

	glob->boundParams = boundParams;
	glob->subplans = NIL;
	glob->subroots = NIL;
	glob->rewindPlanIDs = NULL;
	glob->finalrtable = NIL;
	glob->finalrowmarks = NIL;
	glob->resultRelations = NIL;
	glob->relationOids = NIL;
	glob->invalItems = NIL;
	glob->nParamExec = 0;
	glob->lastPHId = 0;
	glob->lastRowMarkId = 0;
	glob->transientPlan = false;

	/* Determine what fraction of the plan is likely to be scanned */
	if (cursorOptions & CURSOR_OPT_FAST_PLAN)
	{
		/*
		 * We have no real idea how many tuples the user will ultimately FETCH
		 * from a cursor, but it is often the case that he doesn't want 'em
		 * all, or would prefer a fast-start plan anyway so that he can
		 * process some of the tuples sooner.  Use a GUC parameter to decide
		 * what fraction to optimize for.
		 */
		tuple_fraction = cursor_tuple_fraction;

		/*
		 * We document cursor_tuple_fraction as simply being a fraction, which
		 * means the edge cases 0 and 1 have to be treated specially here.	We
		 * convert 1 to 0 ("all the tuples") and 0 to a very small fraction.
		 */
		if (tuple_fraction >= 1.0)
			tuple_fraction = 0.0;
		else if (tuple_fraction <= 0.0)
			tuple_fraction = 1e-10;
	}
	else
	{
		/* Default assumption is we need all the tuples */
		tuple_fraction = 0.0;
	}
	/* primary planning entry point (may recurse for subqueries) */
	top_plan = ppg_subquery_planner(glob, parse, NULL,
								false, tuple_fraction, &root) ;

	/*
	 * If creating a plan for a scrollable cursor, make sure it can run
	 * backwards on demand.  Add a Material node at the top at need.
	 */
	if (cursorOptions & CURSOR_OPT_SCROLL)
	{
		if (!ExecSupportsBackwardScan(top_plan))
			top_plan = materialize_finished_plan(top_plan);
	}

	/* final cleanup of the plan */
	Assert(glob->finalrtable == NIL);
	Assert(glob->finalrowmarks == NIL);
	Assert(glob->resultRelations == NIL);
	finalrtable = getPPGRTEfromQuery(parse, FDW_handler);
	glob->finalrtable = NIL;
	//traceNode(INFO, "\n output plan %s\n", top_plan);
	top_plan = set_plan_references(root, top_plan);
	/* ... and the subplans (both regular subplans and initplans) */
	Assert(list_length(glob->subplans) == list_length(glob->subroots));
	/*forboth(lp, glob->subplans, lr, glob->subroots)
	{
		Plan	   *subplan = (Plan *) lfirst(lp);
		PlannerInfo *subroot = (PlannerInfo *) lfirst(lr);
		lfirst(lp) = set_plan_references(subroot, subplan);
	}*/
	/* build the PlannedStmt result */
	result = makeNode(PlannedStmt);
	result->commandType = parse->commandType;
	result->queryId = parse->queryId;
	result->hasReturning = (parse->returningList != NIL);
	result->hasModifyingCTE = parse->hasModifyingCTE;
	result->canSetTag = parse->canSetTag;
	result->transientPlan = glob->transientPlan;
	result->planTree = top_plan;
	result->rtable = list_make1(finalrtable);
	result->resultRelations = glob->resultRelations;
	result->utilityStmt = parse->utilityStmt;
	result->subplans = glob->subplans;
	result->rewindPlanIDs = glob->rewindPlanIDs;
	result->rowMarks = glob->finalrowmarks;
	result->relationOids = glob->relationOids;
	result->invalItems = glob->invalItems;
	result->nParamExec = glob->nParamExec;

	return result;

}

void ppg_planner_init()
{	
	FDW_handler = (FdwRoutine *)ppg_fdw_handler(NULL);
	next_planner_hook = planner_hook;
	planner_hook = ppg_planner;	
}
