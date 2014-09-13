/*-------------------------------------------------------------------------
 *
 * ppg_subselect.c
 *	  Planning routines for subselects and parameters. 
 *	  Borrowed from PG but small change
 *
 *
 * IDENTIFICATION
 *	  contrib/ppg_fdw/ppg_subselect.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "executor/executor.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/subselect.h"
#include "optimizer/var.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "parser/parse_oper.h"
#include "rewrite/rewriteManip.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "lib/stringinfo.h"

#include "util.h"

typedef struct ppg_process_sublinks_context
{
    PlannerInfo *root;
    bool        isTopQual;
} ppg_process_sublinks_context;   

static void handleJt(Query*parse, Node* jtnode, SubPlanPath *planPath);

static void handleSublink(Node *node , SubPlanPath *planPath);

static void handle_EXPR_sublink(SubLink *sublink, SubPlanPath *planPath);

static Node* extract_quals_of_level (Node **node, int level);

static Node* ppg_process_sublinks_mutator(Node *node, ppg_process_sublinks_context *context);

static Node* ppg_make_subplan(PlannerInfo *root, Query *orig_subquery, SubLinkType subLinkType, Node *testexpr, bool isTopQual);


static void handleJt(Query*parse, Node* jtnode, SubPlanPath *planPath) 
{
	if (jtnode == NULL)
		return ;
	if (IsA(jtnode, RangeTblRef)) {
		int varno = ((RangeTblRef *) jtnode)->rtindex;
		RangeTblEntry *rte = rt_fetch(varno, parse->rtable);
		if (rte->rtekind == RTE_SUBQUERY) {
			Query* subquery = rte->subquery; 
			PlannerInfo *subroot;
			List	    *outTlist;
			StringInfoData buf;
			initStringInfo(&buf);
			// Give it a unique name 
			appendStringInfo(&buf, "tmp_table_%s_%ld", rte->alias->aliasname, random());
			rte->alias->aliasname = (char*) palloc((strlen(buf.data)+1)*sizeof(char));
			memcpy(rte->alias->aliasname, buf.data, strlen(buf.data));
			rte->alias->aliasname[strlen(buf.data)] = 0;

			Plan* sub_plan = ppg_subquery_planner(planPath->root->glob, subquery, planPath->root, false, 0.0, &subroot, &outTlist);
			sub_plan = set_plan_references(subroot, sub_plan);
			planPath->root->glob->subplans = lappend(planPath->root->glob->subplans, sub_plan);
			planPath->root->glob->subroots = lappend(planPath->root->glob->subroots, subroot);
			
			subquery->targetList = outTlist;
			SubPlanPath *subplanPath = (SubPlanPath *) palloc(sizeof(SubPlanPath));
			subplanPath->source = (Node*)rte;
			subplanPath->type = InFrom ;
			subplanPath->planID = list_length(planPath->root->glob->subplans);
			subplanPath->subPlanList = NULL;
			planPath->subPlanList = lappend(planPath->subPlanList, subplanPath);
		
		} 	
	} else if (IsA(jtnode, FromExpr)) {
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;
		foreach(l, f->fromlist) 
		{
			handleJt(parse, lfirst(l), planPath);
		}
	} else if (IsA(jtnode, JoinExpr)) {
		JoinExpr   *j = (JoinExpr *) jtnode;
		handleJt(parse, j->larg, planPath);
		handleJt(parse, j->rarg, planPath);
	} else {
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
		return ;
	}
}


static void handleSublink(Node *node , SubPlanPath *planPath)
{
        if (node == NULL)
                return ;
        if (IsA(node, SubLink))        
        {                     
		SubLink    *sublink = (SubLink *) node;   
            	handleSublink(sublink->testexpr, planPath);
		if ((sublink->subLinkType == ANY_SUBLINK) ||(sublink->subLinkType == EXISTS_SUBLINK)){
			elog(ERROR,"This ANY or EXISTS sublink is not supported");
		} else if (sublink->subLinkType == ALL_SUBLINK) {
			elog(ERROR,"This ALL sublink is not supported");
		} else if (sublink->subLinkType == ROWCOMPARE_SUBLINK) {
			elog(ERROR,"This ROW compare sublink is not supported");
		} else if (sublink->subLinkType == EXPR_SUBLINK) {
			handle_EXPR_sublink(sublink, planPath);
			return ;
		}
        }

        if (and_clause(node))
    	{
        	ListCell   *l;
           	foreach(l, ((BoolExpr *) node)->args) {
			handleSublink(lfirst(l), planPath);
		}
        }

        if (or_clause(node))
        {
                ListCell   *l;
                foreach(l, ((BoolExpr *) node)->args)
                {
                        handleSublink(lfirst(l), planPath);
                }
        }
        expression_tree_walker(node, handleSublink, (void *) planPath);
	return;
}

void getSubPlanPath(Query *parse , SubPlanPath *planPath)
{
	FromExpr  *jointree = parse->jointree;
	ListCell *lc;
	foreach(lc, jointree->fromlist) {
		handleJt(parse, lfirst(lc), planPath);
	}
	if (parse->hasSubLinks  && jointree->quals != NULL) {
		handleSublink(jointree->quals, planPath);
	}
}

static Node* extract_quals_of_level (Node **expr, int level) 
{
	List *result = NULL;
	Node		*cell;
	Node		*node = *expr;
	if (node == NULL)
		return NULL;
	if (not_clause(node)) {
		Node *newNode = extract_quals_of_level (&node, level);
		if (newNode != NULL) {
			((BoolExpr *)(node))->args = list_make1(makeBoolConst(false, true));
			return (Node*)make_notclause((Expr*)newNode);
		}
	} else if(IsA(node, OpExpr)) {
		if (contain_vars_of_level(node, level)) {
			*expr = NULL;
			return node;
		}
	}
	if (IsA(node, RangeTblRef)) {
		return NULL;
	} else if (IsA(node, FromExpr)) {
		FromExpr   *f = (FromExpr *) node;
		ListCell   *l;
		if (length(f->fromlist) ==0) {
			return NULL;
		}
		foreach(l, f->fromlist) 
		{
			cell = extract_quals_of_level ((Node**)(&(lfirst(l))), level);
			if(cell!= NULL) {
				result = lappend(result, cell);
			}
		}
		if (f->quals != NULL) {
			cell = extract_quals_of_level(&(f->quals),level);
			if(cell!= NULL) {
				result = lappend(result, cell);
			}		
		}
	}
	else if (IsA(node, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) node;
		cell = extract_quals_of_level((Node**)(&(j->larg)),level);
		if(cell!= NULL) {
			result = lappend(result, cell);
		}
		cell = extract_quals_of_level((Node**)(&(j->rarg)),level);
		if(cell!= NULL) {
			result = lappend(result, cell);
		}
		if ( j->quals != NULL)
		{
			cell = extract_quals_of_level((Node**)(&(j->quals)),level);
			if(cell!= NULL) {
				result = lappend(result, cell);
			}
		}
	}
	if (and_clause(node) ||(or_clause(node)))
	{
		/* Recurse into AND clause */
		List	   *newclauses = NIL;
		List	   *oldclauses = NIL;
		ListCell   *l;

		foreach(l, ((BoolExpr *) node)->args)
		{
			Node	   *oldclause = (Node *) lfirst(l);
			Node	   *newclause;

			newclause = extract_quals_of_level((Node**)(&oldclause), level);
			if (newclause != NULL) {
				newclauses = lappend(newclauses, newclause);
			} else {
				oldclauses = lappend(oldclauses, oldclause);
			}
		}
		/* We might have got back fewer clauses than we started with */
		if (newclauses == NIL) {
			return NULL;
		}  else {
			if (length(oldclauses) ==0) {
				oldclauses = lappend(oldclauses, makeBoolConst(true, true));
			}
			((BoolExpr *) node)->args = oldclauses;
			if (list_length(newclauses) == 1) {
				if (and_clause(node)) {
					return (Node *) linitial(newclauses);
				} else {
					return (Node*)make_orclause(newclauses);	
				}
			}
			else {
				if (and_clause(node)) {
					return (Node*)make_andclause(newclauses);
				} else {
					return (Node*)make_orclause(newclauses);	
				}
			}
		}
	}
	return (Node*)result;
}

static void handle_EXPR_sublink(SubLink *sublink, SubPlanPath *planPath)
{
	Query	   *subselect = (Query *) sublink->subselect;
	Query	   *qry = makeNode(Query);
	PlannerInfo *subroot = NULL;
	List	    *outTlist = NIL;
	StringInfoData buf;
	RangeTblEntry *rte = NULL;
	List	   *quals = NIL;
	RangeTblRef *rtr = NULL;
	Var	*var = NULL;
	TargetEntry * oldTe = NULL;
	TargetEntry * newTe = NULL;
	ListCell *lc1;

	if (subselect->jointree != NULL && contain_vars_of_level((Node *) subselect->jointree, 1)) {
		quals = (List*)extract_quals_of_level ((Node **)(&(subselect->jointree)), 1);
	}

	if (subselect->havingQual != NULL && contain_vars_of_level((Node *) subselect->havingQual, 1)) {
		quals = list_concat(quals, (List*)extract_quals_of_level ((Node **)(&(subselect->havingQual)), 1));
	}
	List 		*vars = NIL;
	vars = pull_vars_of_level((Node*)quals, 0);
	if(vars != NULL) {
		List	*addTargetList = NIL;
		AttrNumber resno = length(subselect->targetList)+1;
		foreach(lc1, vars) {
			Var	*var = lfirst(lc1);
			ListCell *lc2;
			bool	find = false;
			foreach(lc2, subselect->targetList) {
				TargetEntry* tle = lfirst(lc2);
				if (IsA(tle->expr,Var) &&((Var*) (tle->expr))->varattno == var->varattno &&
					((Var*) (tle->expr))->varno == var->varno) {
					find = true;
					break;
				}
			}
			if (!find) {
				RangeTblEntry *rte = rt_fetch(var->varno, subselect->rtable);
				char		*colname = get_relid_attribute_name(rte->relid, var->varattno);
				TargetEntry *newTle = (TargetEntry *)makeTargetEntry(copyObject(var), resno, colname, false);
				addTargetList = lappend(addTargetList, newTle);
				resno++;
			}
		}
		subselect->targetList = list_concat(subselect->targetList, addTargetList);
		if (subselect->hasAggs) {
			// add a group and revise the groupref
			int SortGroupRef = 0;
			foreach(lc1, subselect->targetList) {
				Index	ref = ((TargetEntry *) lfirst(lc1))->ressortgroupref;
				if (ref > SortGroupRef) {
					SortGroupRef = ref;
				}
			}
			SortGroupRef++;
			foreach(lc1, addTargetList) {
				TargetEntry* tle = lfirst(lc1);
				tle->ressortgroupref = SortGroupRef;
				if(!targetIsInSortList(tle, InvalidOid, subselect->groupClause) ) {
					SortGroupClause *grpcl = makeNode(SortGroupClause);
					Oid         sortop;
        				Oid         eqop;
        				bool        hashable;
					Oid         restype = exprType((Node *) tle->expr);
        				get_sort_group_operators(restype, false, true, false, &sortop, &eqop, NULL, &hashable);
        				grpcl->tleSortGroupRef = SortGroupRef;
	        			grpcl->eqop = eqop;
        				grpcl->sortop = sortop;
        				grpcl->nulls_first = false;     /* OK with or without sortop */
        				grpcl->hashable = hashable;
        				subselect->groupClause = lappend(subselect->groupClause, grpcl);
					SortGroupRef++;
				}
			}
		}
	}
	rte = addRangeTableEntryForSubquery(NULL,
										subselect,
										makeAlias("ppg_subquery", NIL),
										false,
										false);
	rte->alias = copyObject(rte->eref);

	initStringInfo(&buf);
	// Give it a unique name 
	appendStringInfo(&buf, "tmp_table_%s_%ld", rte->alias->aliasname, random());
	rte->alias->aliasname = (char*) palloc((strlen(buf.data)+1)*sizeof(char));
	memcpy(rte->alias->aliasname, buf.data, strlen(buf.data));
	rte->alias->aliasname[strlen(buf.data)] = 0;
	/*planPath->root->parse->rtable = lappend(planPath->root->parse->rtable, rte);
	rtindex = list_length(planPath->root->parse->rtable);*/
	pfree(buf.data);

	Plan* sub_plan = ppg_subquery_planner(planPath->root->glob, subselect, planPath->root, false, 0.0, &subroot, &outTlist);
	sub_plan = set_plan_references(subroot, sub_plan);
	planPath->root->glob->subplans = lappend(planPath->root->glob->subplans, sub_plan);
	planPath->root->glob->subroots = lappend(planPath->root->glob->subroots, subroot);
	subselect->targetList = outTlist;
	SubPlanPath *subplanPath = (SubPlanPath *) palloc(sizeof(SubPlanPath));
	subplanPath->source = (Node*)rte;
	subplanPath->type = InSublink ;
	subplanPath->planID = list_length(planPath->root->glob->subplans);
	subplanPath->subPlanList = NULL;
	planPath->subPlanList = lappend(planPath->subPlanList, subplanPath);

	// OK create a new query for the sublink
	qry->commandType = CMD_SELECT;
	rtr = makeNode(RangeTblRef);
	qry->rtable = list_make1(rte);
	rtr->rtindex = 1;	
	vars = pull_vars_of_level((Node*)quals, 0);
	foreach(lc1, vars) {
		Var	*var = lfirst(lc1);
		var->varno = 1;
	}
	/*char *s = nodeToString(quals);
    	elog(INFO, "\n quals in sublink  %s\n", pretty_format_node_dump(s));*/

	qry->jointree = makeFromExpr(list_make1(rtr), (Node*)quals);
	oldTe = lfirst(list_head(subselect->targetList));
	var = makeVar(1, 1, exprType(((Node*)(oldTe->expr))), exprTypmod(((Node*)(oldTe->expr))), -1,  0);
	newTe = makeTargetEntry((Expr*)var, 1, oldTe->resname, false);
	qry->targetList = list_make1(newTe);
	qry->havingQual = NULL;
	qry->sortClause = NIL;
	qry->groupClause = NIL;
	qry->distinctClause = NIL;
	qry->hasDistinctOn = false;
	qry->limitOffset = NULL;
	qry->hasSubLinks = false;
	qry->hasWindowFuncs = false;
	qry->hasAggs = false;
	sublink->subselect = (Node*)qry;

	return;
}

Node* ppg_process_sublink_in_having(PlannerInfo *root, Node *node, bool isQual)
{
	ppg_process_sublinks_context context;
	context.root = root; 
	context.isTopQual = isQual;
	return ppg_process_sublinks_mutator(node, &context);
}
static Node * ppg_process_sublinks_mutator(Node *node, ppg_process_sublinks_context *context)
{
	ppg_process_sublinks_context locContext;	
	locContext.root = context->root;

	if (node == NULL)
    	return NULL;
	if (IsA(node, SubLink)){                     
		SubLink    *sublink = (SubLink *) node;   
        Node       *testexpr;
		locContext.isTopQual = false;
		if ((sublink->subLinkType == ANY_SUBLINK) ||(sublink->subLinkType == EXISTS_SUBLINK))
		{
			elog(ERROR,"This ANY or EXISTS sublink is not supported");

		} else if (sublink->subLinkType == ALL_SUBLINK) {
			elog(ERROR,"This ALL sublink is not supported");
		} else if (sublink->subLinkType == ROWCOMPARE_SUBLINK) {
			elog(ERROR,"This ROW compare sublink is not supported");
		} else if (sublink->subLinkType == EXPR_SUBLINK) {
			//char *s = nodeToString(sublink);
    			//elog(INFO, "\n sublink  %s\n", pretty_format_node_dump(s));
    		testexpr = ppg_process_sublinks_mutator(sublink->testexpr, &locContext);
			return ppg_make_subplan(context->root, (Query *) sublink->subselect , sublink->subLinkType,
									testexpr, context->isTopQual);
			
		}
	}

	if (and_clause(node)) {
		List       *newargs = NIL;
        ListCell   *l;
		locContext.isTopQual = false;
        foreach(l, ((BoolExpr *) node)->args)
        {
			Node       *newarg = ppg_process_sublinks_mutator(lfirst(l), &locContext);
			if (and_clause(newarg))
                newargs = list_concat(newargs, ((BoolExpr *) newarg)->args);
            else
                newargs = lappend(newargs, newarg);
		}
		 return (Node *) make_andclause(newargs);
    }

	if (or_clause(node))
    {
    	List       *newargs = NIL;
        ListCell   *l;

		locContext.isTopQual = false;
        foreach(l, ((BoolExpr *) node)->args)
        {
			 Node	*newarg = ppg_process_sublinks_mutator(lfirst(l), &locContext);
			if (or_clause(newarg))
                newargs = list_concat(newargs, ((BoolExpr *) newarg)->args);
            else
                newargs = lappend(newargs, newarg);
        }
		return (Node *) make_orclause(newargs);
	}
	locContext.isTopQual = false;
    return expression_tree_mutator(node, ppg_process_sublinks_mutator, (void *) &locContext);
}

static Node * 
ppg_make_subplan(PlannerInfo *root, Query *subquery, SubLinkType subLinkType, Node *testexpr, bool isTopQual)
{
	Plan       *plan;
	PlannerInfo *subroot;
	bool        isInitPlan;
	List       *plan_params;
	Node       *result;
	SubPlan    *splan;
	TargetEntry *tent = NULL;
	ListCell   *lc;
	List	    *outTlist;
	plan = ppg_subquery_planner(root->glob, subquery, root,	false, 0.0, &subroot, &outTlist);
	plan = set_plan_references(subroot, plan);
	subquery->targetList = outTlist;
 	tent = (TargetEntry *) linitial(plan->targetlist);
	splan = makeNode(SubPlan);
	splan->subLinkType = subLinkType;
	splan->testexpr = NULL;
	splan->paramIds = NIL;
	if (tent != NULL && !(tent->resjunk)) {
		splan->firstColType =  exprType((Node *) tent->expr);
		splan->firstColTypmod = exprTypmod((Node *) tent->expr);
		splan->firstColCollation = exprCollation((Node *) tent->expr);
	} else {
		splan->firstColType = VOIDOID;
		splan->firstColTypmod = -1;
		splan->firstColCollation = InvalidOid;
	}
	plan_params = root->plan_params;
	root->plan_params = NIL;
	foreach(lc, plan_params)
	{
		PlannerParamItem *pitem = (PlannerParamItem *) lfirst(lc);
		Node       *arg = pitem->item;
		if (IsA(arg, PlaceHolderVar) ||IsA(arg, Aggref)) {
			arg = ppg_process_sublink_in_having(root, arg, false);
		}
		splan->parParam = lappend_int(splan->parParam, pitem->paramId);
		splan->args = lappend(splan->args, arg);
	}
	if (splan->parParam == NIL && subLinkType == EXPR_SUBLINK) {
		Assert(!tent->resjunk);
		Oid arraytype = get_array_type(exprType((Node *) tent->expr));
		if (!OidIsValid(arraytype)) {
			elog(ERROR, "could not find array type for datatype %s",
				format_type_be(exprType((Node *) tent->expr)));
		}
		Param      *prm = makeNode(Param);
    		prm->paramkind = PARAM_EXEC;
	    	prm->paramid = root->glob->nParamExec++;
    		prm->paramtype = splan->firstColType; 
	   	prm->paramtypmod = splan->firstColTypmod;
    		prm->paramcollid = splan->firstColCollation;
	    	prm->location = -1; 
		splan->setParam = list_make1_int(prm->paramid);
		isInitPlan = true;
		result = (Node *) prm;
	} else {
		elog(ERROR, "Unable to handle this case in sublink, to be done \n");
	}
	root->glob->subplans = lappend(root->glob->subplans, plan);
	root->glob->subroots = lappend(root->glob->subroots, subroot);
	splan->plan_id = list_length(root->glob->subplans);
	if (isInitPlan) {
		root->init_plans = lappend(root->init_plans, splan);
	}
	if (isInitPlan)
    	{
        	ListCell   *lc;
        	int         offset;

	        splan->plan_name = palloc(32 + 12 * list_length(splan->setParam));
        	sprintf(splan->plan_name, "InitPlan %d (returns ", splan->plan_id);
	        offset = strlen(splan->plan_name);
        	foreach(lc, splan->setParam)
        	{
			sprintf(splan->plan_name + offset, "$%d%s",
                    	lfirst_int(lc),
			lnext(lc) ? "," : "");
	            	offset += strlen(splan->plan_name + offset);
        	}
        	sprintf(splan->plan_name + offset, ")");
    	}
    	else
    	{
        	splan->plan_name = palloc(32);
        	sprintf(splan->plan_name, "SubPlan %d", splan->plan_id);
    	}
	cost_subplan(root, splan, plan);
	return result;
}


bool handleAggExprInHaving(Node *node, havingAggContext* context)
{
	if (node == NULL) {
		return false;
	}

	switch (nodeTag(node))
	{
		case T_OpExpr:
		case T_DistinctExpr:	/* struct-equivalent to OpExpr */
		case T_NullIfExpr:		/* struct-equivalent to OpExpr */
		{
			OpExpr	   *expr = (OpExpr *) node;
        		ListCell   *l;
			List *newArgs = NIL;
	        	foreach(l, expr->args) {
				if (nodeTag(lfirst(l)) == T_Aggref) {
					if (context->action == Extract) {
						context->oldAgg = (Aggref*)lfirst(l);
						break;
					} else if (context->action == Replace) {
						Assert(lfirst(l) == context->oldAgg) ;
						newArgs = lappend(newArgs, context->newAgg);
						continue;
					} else {
						elog(ERROR, "Unkown action when handle agg expr in having clause\n");
					} 
				}
				if (context->action == Replace){
					newArgs = lappend(newArgs, lfirst(l));
				}
			}
			if (context->action == Replace) {
				// we need to modify all fields of expr 
				char * opName = get_opname(expr->opno);
				List* opNameStr = list_make1(makeString(opName)); 
				Node* leftArg = list_nth(newArgs, 0);
				Node* rightArg = (length(newArgs) == 2) ? list_nth(newArgs, 1) : NULL;
				OpExpr	   *tmpExpr = (OpExpr *) make_op(NULL, opNameStr, leftArg, rightArg, expr->location);
			
				expr->opno = tmpExpr->opno;
				expr->opfuncid = tmpExpr->opfuncid;
				expr->opresulttype = tmpExpr->opresulttype;
				expr->opretset = tmpExpr->opretset;
				expr->args = (List*)eval_const_expressions(NULL, (Node*)(tmpExpr->args));
			}
			return true;
		}
		default:
			break;
	}

	if (and_clause(node)) {
        ListCell   *l;
        foreach(l, ((BoolExpr *) node)->args)
        {
			if (handleAggExprInHaving(lfirst(l), context)) {
				return true;
			}
		}
    }
	if (or_clause(node))
    {
        ListCell   *l;
        foreach(l, ((BoolExpr *) node)->args)
        {
			if (handleAggExprInHaving(lfirst(l), context)) {
				return true;
			}
	    }
	}
    return expression_tree_walker(node, handleAggExprInHaving, (void *) context);
}
