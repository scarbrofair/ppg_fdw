#include "postgres.h"

#include "postgres.h"

#include <limits.h>

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
#include "parser/parsetree.h"
#include "parser/parse_func.h"
#include "parser/parse_oper.h"
#include "rewrite/rewriteManip.h"
#include "utils/rel.h"
#include "utils/syscache.h"

#include "util.h"

static bool canJtPush(Query* parse,Node* jtnode,FdwRoutine *fdw_handler);

static bool canQualPush(Query* root,Node* qual,FdwRoutine *fdw_handler);

static RangeTblEntry *getPPGRTEfromJt(Query*parse, Node* jtnode);

static RangeTblEntry *getPPGRTEfromQual(Query*parse, Node* qual);

static RangeTblEntry *getPPGRTEfromJt(Query*parse,Node* jtnode)
{
        RangeTblEntry *rte = NULL;
        if (jtnode == NULL)
                return NULL;
        if (IsA(jtnode, RangeTblRef))
        {
                int                     varno = ((RangeTblRef *) jtnode)->rtindex;
                RangeTblEntry *rte = rt_fetch(varno, parse->rtable);
                if (rte->rtekind == RTE_SUBQUERY) 
                {
                        return getPPGRTEfromQuery(rte->subquery);
                } else if (rte->rtekind == RTE_RELATION && rte->relkind == RELKIND_FOREIGN_TABLE){
                        FdwRoutine *routine = GetFdwRoutineByRelId(rte->relid); 
                        if (routine != NULL) { //&& ((long)(routine->BeginForeignScan) == ((long)(fdw_handler->BeginForeignScan)))) {
                                return rte;
                        }
                }
                rte = NULL;
        } else if (IsA(jtnode, FromExpr)) {
                FromExpr   *f = (FromExpr *) jtnode;
                ListCell   *l;
                foreach(l, f->fromlist) 
                {
                        rte =  getPPGRTEfromJt(parse, lfirst(l));
                        if (rte != NULL) {
                                return rte;
                        }
                }
                if (parse->hasSubLinks && rte == NULL && f->quals != NULL) {
                        rte = getPPGRTEfromQual(parse, f->quals);
                }
        }
        else if (IsA(jtnode, JoinExpr))
        {
                JoinExpr   *j = (JoinExpr *) jtnode;

                rte = getPPGRTEfromJt(parse, j->larg);
                if (!rte)
                {
                        rte = getPPGRTEfromJt(parse, j->rarg);
                }
                if (parse->hasSubLinks && rte == NULL && j->quals != NULL)
                {
                        rte = getPPGRTEfromQual(parse,j->quals);
                }
        }
        return rte ;
}

static RangeTblEntry *getPPGRTEfromQual(Query*parse, Node* node)
{
        RangeTblEntry *rte = NULL;
        if (node == NULL )
        {
                return NULL;
        }
        if (IsA(node, SubLink)) {
                SubLink    *sublink = (SubLink *) node;
                Query      *subselect = (Query *) (sublink->subselect);
                rte = getPPGRTEfromQuery(subselect);
        } else if (IsA(node, BoolExpr)) {
                if (((BoolExpr*)node)->boolop == NOT_EXPR) {
                        Node   *sublink = (Node *) get_notclausearg((Expr *) node);
                        rte = getPPGRTEfromQual(parse, sublink);
                } else if (IsA(node,BoolExpr)) {
                        ListCell   *l;
                        foreach(l, ((BoolExpr *) node)->args)
                        {
                                Node       *clause = (Node *) lfirst(l);
                                rte = getPPGRTEfromQual(parse,clause);
                                if (rte != NULL) {
                                        break;
                                }
                        }
                }
        }
        return rte;
}

RangeTblEntry *getPPGRTEfromQuery(Query *parse)
{
        RangeTblEntry *rte = NULL;
        // first chech the jointree
        Node* jtnode = (Node*) parse->jointree;
        if (jtnode != NULL )
        {
                rte = getPPGRTEfromJt(parse, jtnode);
        }
        if (rte == NULL && parse->havingQual != NULL) {
                rte = getPPGRTEfromQual(parse, parse->havingQual);
        }
        return rte;
}


/*
 *can push join tree to ppg_fdw
 * */
static bool canJtPush(Query*parse,Node* jtnode,FdwRoutine *fdw_handler) 
{
	bool canPush = true;
	FdwRoutine * routine = NULL;
	if (jtnode == NULL)
		return true;
	if (IsA(jtnode, RangeTblRef)) {
		int varno = ((RangeTblRef *) jtnode)->rtindex;
		RangeTblEntry *rte = rt_fetch(varno, parse->rtable);
		if (rte->rtekind == RTE_SUBQUERY) {
			Query* subquery = rte->subquery; 
			if (!IsA(subquery,Query) ||subquery->commandType != CMD_SELECT 
				||subquery->utilityStmt != NULL || subquery->setOperations) {
				canPush = false; // we only push simple subquery to ppg_fdw directly, will support set operations later
			} else {
				canPush =canAllPush (subquery, fdw_handler) ;
			}
		} else if (rte->rtekind == RTE_RELATION && rte->relkind == RELKIND_FOREIGN_TABLE) {
			routine = GetFdwRoutineByRelId(rte->relid);
			if ((routine != NULL) &&　routine == fdw_handler) {
				//	&& ((long)(routine->BeginForeignScan) == ((long)(fdw_handler->BeginForeignScan)))) {
				canPush = true;;
			}
		} else {
			canPush = false;
		}
	} else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;
		if (length(f->fromlist) == 0) {
			return false;
		}
		foreach(l, f->fromlist) 
		{

			if (canPush) {
				canPush &= canJtPush(parse, lfirst(l),fdw_handler);
				if (!canPush) {
					return false;
				}
			}
		}
		if (parse->hasSubLinks  && f->quals != NULL) {
			canPush &= canQualPush(parse, f->quals,fdw_handler);
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		canPush &= canJtPush(parse, j->larg,fdw_handler);
		if (canPush) 
		{		
			canPush &= canJtPush(parse, j->rarg,fdw_handler);
		}
		if (parse->hasSubLinks && canPush && j->quals != NULL)
		{
			canPush = canQualPush(parse,j->quals,fdw_handler);
		}
	}
	else {
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
		return false;
	}
	return canPush;
}
/*
 *can push sublink to ppg_fdw
 * */
static bool canQualPush(Query*root,Node*node, FdwRoutine *fdw_handler)
{
	bool canPush = true;
	if (node == NULL) {
		return true;
	}
	if (IsA(node, SubLink)) {
		SubLink    *sublink = (SubLink *) node;
		if (sublink->subLinkType == ANY_SUBLINK) {
			Query	   *subselect = (Query *) sublink->subselect;

			Assert(sublink->subLinkType == ANY_SUBLINK);
			return canAllPush(subselect, fdw_handler);

		} else if (sublink->subLinkType == EXISTS_SUBLINK) {
			Query *subselect = (Query *) sublink->subselect;

			Assert(sublink->subLinkType == EXISTS_SUBLINK);

			if (subselect->commandType != CMD_SELECT)
				return false;

			if (subselect->jointree->fromlist == NIL)
				return false;

			return canAllPush(subselect, fdw_handler);

		} else {
			canPush = false;
		}

	} else if ((node!=NULL)&&IsA(node,BoolExpr)&&((BoolExpr*)node)->boolop==NOT_EXPR) {
		SubLink    *sublink = (SubLink *) get_notclausearg((Expr *) node);

		if (sublink && IsA(sublink, SubLink)) {
			if (sublink->subLinkType == EXISTS_SUBLINK)
			{	
				Query	   *subselect = (Query *) sublink->subselect;
				if (subselect->cteList)
					return false;

				if (subselect->commandType != CMD_SELECT ||
					subselect->setOperations)
					return false;

				if (subselect->jointree->fromlist == NIL)
					return false;

				return canAllPush(subselect, fdw_handler);

			} else {
				return false;
			}
		}

	} else if ((node!=NULL)&&IsA(node,BoolExpr)&&((BoolExpr*)node)->boolop==AND_EXPR) {
		ListCell   *l;
		foreach(l, ((BoolExpr *) node)->args)
		{
			Node	   *clause = (Node *) lfirst(l);

			if (!canQualPush(root,clause,fdw_handler)) {
				return false;
			}
		}
	}
	return canPush;
	
}
/*
 *Can all of the plan  push to ppg_fdw 
 * */
bool canAllPush(Query *parse, FdwRoutine *fdw_handler)
{
	bool all_ppg_fdw = true;
	Node* jtnode = parse->jointree;
	if (jtnode != NULL) {
		all_ppg_fdw &= canJtPush(parse, jtnode, fdw_handler);
	}
	if (all_ppg_fdw && parse->havingQual) {
		all_ppg_fdw &= canQualPush(parse, parse->havingQual, fdw_handler);
	}
	return all_ppg_fdw;
}



/*
 * lookup the name of function with specified oid
 */
char* getFuncName(Oid fnoid)
{
	HeapTuple   proctup;
	Form_pg_proc procform;
	char	*proname = NULL;
	char 	*ret = NULL;
	proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(fnoid));
	if (!HeapTupleIsValid(proctup)) {
		elog(ERROR, "cache lookup failed for function %u",fnoid);
	}
	procform = (Form_pg_proc) GETSTRUCT(proctup);
	proname = NameStr(procform->proname);
	ReleaseSysCache(proctup);
	ret = palloc0(sizeof(AttrNumber) * (strlen(proname)+1));
	strcpy(ret, proname);
	return ret;
}
