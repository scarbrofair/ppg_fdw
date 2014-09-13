#ifndef PPG_UTIL_H
#define PPG_UTIL_H

#include "nodes/nodes.h"
#include "nodes/parsenodes.h"
#include "nodes/relation.h"
#include "foreign/fdwapi.h"

typedef enum
{
	RoundRobin,  /* random chose a node and insert record to remote database*/
	HashRobin,  /* get the hash value of some fields  and then distribute to all the node*/
	All        /* copy data to all the remote database*/
} DistributeMethod;

typedef enum
{
	InFrom,  /* subquery in from clause */
	InSublink,  /* subquery in sublink clause */
	InHaving        /* in Having clause */
} SubplanType;

typedef struct SubQueryPlan
{
	int 	subplanIndex;
	char	*createTable;
	List	*typeID;
	char	*insertSQL;
	DistributeMethod dmethod;
} SubQueryPlan;

typedef struct SubPlanPath
{
	PlannerInfo *root;
	Node	*source;
	int16   planID;
	SubplanType	type;
	List	*subPlanList;
	int64	outRows;		// The estimated output rows number  of this plan path
	int64	rowSize;
} SubPlanPath;

typedef enum
{
	Extract,  /* extract add expr in Having clause and store it int oldAgg */
	Replace        /* repalce agg expr (oldAgg) in Having clause with newAgg */
} havingAggAction;

typedef struct havingAggContext
{
	Aggref	*oldAgg;
	Aggref	*newAgg;
	havingAggAction	action;
} havingAggContext;

#define traceNode(level, formatString, node)  \
        do { \
                char *s = nodeToString(node);\
                elog(level, formatString, pretty_format_node_dump(s));\
        } while(0)



extern char* getFuncName(Oid fnoid);

extern void ppg_pull_up_sublinks(PlannerInfo *root);

extern void createSubplan(SubQueryPlan* subplan, RangeTblEntry *rte);

extern void getSubPlanPath(Query *parse, SubPlanPath *planPath); 

//extern Node* insertSubplan2Sublink(Node *node , Plan *subplan);
//
extern Node* ppg_process_sublink_in_having(PlannerInfo *root, Node *node, bool isQual) ;

extern bool handleAggExprInHaving (Node *node, havingAggContext* context);

extern bool canAllPush(Query *parse, FdwRoutine *fdw_handler);

extern RangeTblEntry *getPPGRTEfromQuery(Query *parse, FdwRoutine *fdw_handler);
#endif
