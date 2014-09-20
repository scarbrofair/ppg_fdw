/*-------------------------------------------------------------------------
 *
 * connection.c
 *		  Connection management functions for postgres_fdw
 *
 * Portions Copyright (c) 2012-2013, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		  contrib/postgres_fdw/connection.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "postgres_fdw.h"

#include "access/xact.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "utils/hsearch.h"
#include "utils/memutils.h"


/*
 * Connection cache hash table entry
 *
 * The lookup key in this hash table is the foreign server OID plus the user
 * mapping OID.  (We use just one connection per user per foreign server,
 * so that we can ensure all scans use the same snapshot during a query.)
 *
 * The "conn" pointer can be NULL if we don't currently have a live connection.
 * When we do have a connection, xact_depth tracks the current depth of
 * transactions and subtransactions open on the remote side.  We need to issue
 * commands at the same nesting depth on the remote as we're executing at
 * ourselves, so that rolling back a subtransaction will kill the right
 * queries and not the wrong ones.
 */
typedef struct ConnCacheKey
{
	Oid			serverid;		/* OID of foreign server */
	Oid			userid;			/* OID of local user whose mapping we use */
} ConnCacheKey;

typedef struct ConnCacheEntry
{
	ConnCacheKey key;			/* hash key (must be first) */
	PGconn		**conns;
	//PGconn	   *conn;			/* connection to foreign server, or NULL */
	int			xact_depth;		/* 0 = no xact open, 1 = main xact open, 2 =
								 * one level of subxact open, etc */
	bool		have_prep_stmt; /* have we prepared any stmts in this xact? */
	bool		have_error;		/* have any subxacts aborted in this xact? */
} ConnCacheEntry;

/*
 * Connection cache (initialized on first use)
 */
static HTAB *ConnectionHash = NULL;

/* for assigning cursor numbers and prepared statement numbers */
static unsigned int cursor_number = 0;
static unsigned int prep_stmt_number = 0;

/* tracks whether any work is needed in callback functions */
static bool xact_got_connection = false;

/* prototypes of private functions */
static PGconn** connect_pg_server(ForeignServer *server, UserMapping *user);
static void check_conn_params(const char **keywords, const char **values);
static void configure_remote_session(PGconn *conn);
static void do_sql_command(PGconn *conn, const char *sql);
static void begin_remote_xact(ConnCacheEntry *entry);
static void pgfdw_xact_callback(XactEvent event, void *arg);
static void pgfdw_subxact_callback(SubXactEvent event,
					   SubTransactionId mySubid,
					   SubTransactionId parentSubid,
					   void *arg);
static PGconn * connectDB(const char *URI, const char* user, const char*pwd);

/*
 * Get a PGconn which can be used to execute queries on the remote PostgreSQL
 * server with the user's authorization.  A new connection is established
 * if we don't already have a suitable one, and a transaction is opened at
 * the right subtransaction nesting depth if we didn't do that already.
 *
 * will_prep_stmt must be true if caller intends to create any prepared
 * statements.	Since those don't go away automatically at transaction end
 * (not even on error), we need this flag to cue manual cleanup.
 *
 * XXX Note that caching connections theoretically requires a mechanism to
 * detect change of FDW objects to invalidate already established connections.
 * We could manage that by watching for invalidation events on the relevant
 * syscaches.  For the moment, though, it's not clear that this would really
 * be useful and not mere pedantry.  We could not flush any active connections
 * mid-transaction anyway.
 */
PGconn **
GetConnection(ForeignServer *server, UserMapping *user,
			  bool will_prep_stmt)
{
	return connect_pg_server(server, user);
}

/*
 * Connect to remote server using specified server and user mapping properties.
 */
static PGconn **
connect_pg_server(ForeignServer *server, UserMapping *user)
{
	PGconn	   *volatile conn = NULL;
	PGconn	   ** connArray = NULL;
	char	   **serverURL = NULL;
	char		*userName = NULL;
	char		*pwd	= NULL;
	int 		i = 0;
	ListCell   	*lc;
	serverURL = (const char **) palloc(list_length(server->options) * sizeof(char *));
	connArray = (const PGconn **) palloc(list_length(server->options) * sizeof(PGconn *));
	foreach(lc, server->options)
	{
		DefElem    *d = (DefElem *) lfirst(lc);
		serverURL[i] = defGetString(d);
		i++;
	}
	i = 0;
	foreach(lc, user->options)
	{
		DefElem    *d = (DefElem *) lfirst(lc);
		if (strcmp(d->defname, "user") == 0) {
			userName = defGetString(d);
			i++;
		} else if (strcmp(d->defname, "password") == 0) {
			pwd = defGetString(d);
			i++;
		}
		if (i==2) {
			break;
		}
	}
	/*
	 * Use PG_TRY block to ensure closing connection on error.
	 */
	PG_TRY();
	{
		i = 0;
		while (i < list_length(server->options)) {
			conn = connectDB(serverURL[i], userName, pwd);
			if (!conn || PQstatus(conn) != CONNECTION_OK)
			{
				char	   *connmessage;
				int			msglen;

				/* libpq typically appends a newline, strip that */
				connmessage = pstrdup(PQerrorMessage(conn));
				msglen = strlen(connmessage);
				if (msglen > 0 && connmessage[msglen - 1] == '\n')
					connmessage[msglen - 1] = '\0';
				ereport(ERROR,
			   		(errcode(ERRCODE_SQLCLIENT_UNABLE_TO_ESTABLISH_SQLCONNECTION),
					errmsg("could not connect to server \"%s\"", server->servername),
					errdetail_internal("%s", connmessage)));
			}
			if (!superuser() && !PQconnectionUsedPassword(conn))
				ereport(ERROR,
				  	(errcode(ERRCODE_S_R_E_PROHIBITED_SQL_STATEMENT_ATTEMPTED),
				   	errmsg("password is required"),
				   	errdetail("Non-superuser cannot connect if the server does not request a password."),
				   	errhint("Target server's authentication method must be changed.")));

			configure_remote_session(conn);
			connArray[i++] = conn;
			conn = NULL;
		}
	}
	PG_CATCH();
	{
		/* Release PGconn data structure if we managed to create one */
		if (conn) {
			PQfinish(conn);
			conn = NULL;
		}

		while (i>0) {
			conn = connArray[i--];
			PQfinish(conn);
			conn = NULL;
		}
		pfree(connArray);
		connArray = NULL;
		PG_RE_THROW();
	}
	PG_END_TRY();
	pfree(serverURL);
	return connArray;
}


PGconn* connectDB(const char *URI, const char* user, const char*pwd)
{
    // expected URI format is hostip:port:schema
	char	*host = NULL;
	char	*port = NULL;
	char	*schema = NULL;
	char	*pre = NULL;
	char	*cur = NULL;
	PGconn *conn = NULL;
	char	**keywords = (const char **) palloc(8 * sizeof(char *));
	char	**values = (const char **) palloc(8 * sizeof(char *));

	pre = cur = URI;
	cur = index(pre, ':');
	if (cur == NULL) {
		ereport(ERROR,
			   	(errcode(ERRCODE_SQLCLIENT_UNABLE_TO_ESTABLISH_SQLCONNECTION),
				errmsg("Invalid URI format"),
				errdetail_internal("%s", URI)));
	}
	host = (const char *) palloc(( cur - pre + 1 ) * sizeof(char));
	strncpy(host, pre, cur - pre);
	host[cur-pre] = 0;
	cur++;
	pre = cur;
	cur = index(pre, ':');
	if (cur == NULL) {
		ereport(ERROR,
			   	(errcode(ERRCODE_SQLCLIENT_UNABLE_TO_ESTABLISH_SQLCONNECTION),
				errmsg("Invalid URI format"),
				errdetail_internal("%s", URI)));
	}
	port = (const char *) palloc(( cur - pre + 1) * sizeof(char));
	strncpy(port, pre, cur - pre);
	port[cur-pre] = 0;
	cur++;
	pre = cur;
	cur = strlen(URI)+ URI;
	schema = (const char *) palloc(( cur - pre + 1) * sizeof(char));;
	strncpy(schema, pre, cur - pre);
	schema[cur-pre] = 0;
	//elog(INFO, "connect host %s port %s database_name %s user %s pwd %s\n", host, port, schema, user, pwd);
	keywords[0] = "fallback_application_name";
	values[0] = "postgres_fdw";
	keywords[1] = "client_encoding";
	values[1] = GetDatabaseEncodingName();
	keywords[2] = "host";
	values[2] = host;
	keywords[3] = "port";
	values[3] = port;
	keywords[4] = "dbname";
	values[4] = schema;
	keywords[5] = "user";
	values[5] = user;
	keywords[6] = "password";
	values[6] = pwd;
	keywords[7] = values[7] = NULL;

	conn = PQconnectdbParams(keywords, values, false);
	//conn = PQsetdbLogin(host, port, NULL, NULL, schema, user, pwd);
	pfree(host);
	pfree(port);
	pfree(schema);
	return conn;
}
/*
 * For non-superusers, insist that the connstr specify a password.	This
 * prevents a password from being picked up from .pgpass, a service file,
 * the environment, etc.  We don't want the postgres user's passwords
 * to be accessible to non-superusers.	(See also dblink_connstr_check in
 * contrib/dblink.)
 */
static void
check_conn_params(const char **keywords, const char **values)
{
	int			i;

	/* no check required if superuser */
	if (superuser())
		return;

	/* ok if params contain a non-empty password */
	for (i = 0; keywords[i] != NULL; i++)
	{
		if (strcmp(keywords[i], "password") == 0 && values[i][0] != '\0')
			return;
	}

	ereport(ERROR,
			(errcode(ERRCODE_S_R_E_PROHIBITED_SQL_STATEMENT_ATTEMPTED),
			 errmsg("password is required"),
			 errdetail("Non-superusers must provide a password in the user mapping.")));
}

/*
 * Issue SET commands to make sure remote session is configured properly.
 *
 * We do this just once at connection, assuming nothing will change the
 * values later.  Since we'll never send volatile function calls to the
 * remote, there shouldn't be any way to break this assumption from our end.
 * It's possible to think of ways to break it at the remote end, eg making
 * a foreign table point to a view that includes a set_config call ---
 * but once you admit the possibility of a malicious view definition,
 * there are any number of ways to break things.
 */
static void
configure_remote_session(PGconn *conn)
{
	int			remoteversion = PQserverVersion(conn);

	/* currently, we assume the schema of all the foreign tables is public */
	do_sql_command(conn, "SET search_path = public");

	/*
	 * Set remote timezone; this is basically just cosmetic, since all
	 * transmitted and returned timestamptzs should specify a zone explicitly
	 * anyway.	However it makes the regression test outputs more predictable.
	 *
	 * We don't risk setting remote zone equal to ours, since the remote
	 * server might use a different timezone database.  Instead, use UTC
	 * (quoted, because very old servers are picky about case).
	 */
	do_sql_command(conn, "SET timezone = 'UTC'");

	/*
	 * Set values needed to ensure unambiguous data output from remote.  (This
	 * logic should match what pg_dump does.  See also set_transmission_modes
	 * in postgres_fdw.c.)
	 */
	do_sql_command(conn, "SET datestyle = ISO");
	if (remoteversion >= 80400)
		do_sql_command(conn, "SET intervalstyle = postgres");
	if (remoteversion >= 90000)
		do_sql_command(conn, "SET extra_float_digits = 3");
	else
		do_sql_command(conn, "SET extra_float_digits = 2");
}

/*
 * Convenience subroutine to issue a non-data-returning SQL command to remote
 */
static void
do_sql_command(PGconn *conn, const char *sql)
{
	PGresult   *res;

	res = PQexec(conn, sql);
	if (PQresultStatus(res) != PGRES_COMMAND_OK)
		pgfdw_report_error(ERROR, res, true, sql);
	PQclear(res);
}

/*
 * Start remote transaction or subtransaction, if needed.
 *
 * Note that we always use at least REPEATABLE READ in the remote session.
 * This is so that, if a query initiates multiple scans of the same or
 * different foreign tables, we will get snapshot-consistent results from
 * those scans.  A disadvantage is that we can't provide sane emulation of
 * READ COMMITTED behavior --- it would be nice if we had some other way to
 * control which remote queries share a snapshot.
 */
static void
begin_remote_xact(ConnCacheEntry *entry)
{
/*	int			curlevel = GetCurrentTransactionNestLevel();

	if (entry->xact_depth <= 0)
	{
		const char *sql;

		elog(DEBUG3, "starting remote transaction on connection %p",
			 entry->conns);

		if (IsolationIsSerializable())
			sql = "START TRANSACTION ISOLATION LEVEL SERIALIZABLE";
		else
			sql = "START TRANSACTION ISOLATION LEVEL REPEATABLE READ";
		do_sql_command(entry->conn, sql);
		entry->xact_depth = 1;
	}

	while (entry->xact_depth < curlevel)
	{
		char		sql[64];

		snprintf(sql, sizeof(sql), "SAVEPOINT s%d", entry->xact_depth + 1);
		do_sql_command(entry->conn, sql);
		entry->xact_depth++;
	}*/
}

/*
 * Release connection reference count created by calling GetConnection.
 */
void
ReleaseConnection(PGconn *conn)
{
	/*
	 * Currently, we don't actually track connection references because all
	 * cleanup is managed on a transaction or subtransaction basis instead. So
	 * there's nothing to do here.
	 */
}

/*
 * Assign a "unique" number for a cursor.
 *
 * These really only need to be unique per connection within a transaction.
 * For the moment we ignore the per-connection point and assign them across
 * all connections in the transaction, but we ask for the connection to be
 * supplied in case we want to refine that.
 *
 * Note that even if wraparound happens in a very long transaction, actual
 * collisions are highly improbable; just be sure to use %u not %d to print.
 */
unsigned int
GetCursorNumber(PGconn* conn)
{
	return ++cursor_number;
}

/*
 * Assign a "unique" number for a prepared statement.
 *
 * This works much like GetCursorNumber, except that we never reset the counter
 * within a session.  That's because we can't be 100% sure we've gotten rid
 * of all prepared statements on all connections, and it's not really worth
 * increasing the risk of prepared-statement name collisions by resetting.
 */
unsigned int
GetPrepStmtNumber(PGconn *conn)
{
	return ++prep_stmt_number;
}

/*
 * Report an error we got from the remote server.
 *
 * elevel: error level to use (typically ERROR, but might be less)
 * res: PGresult containing the error
 * clear: if true, PQclear the result (otherwise caller will handle it)
 * sql: NULL, or text of remote command we tried to execute
 *
 * Note: callers that choose not to throw ERROR for a remote error are
 * responsible for making sure that the associated ConnCacheEntry gets
 * marked with have_error = true.
 */
void
pgfdw_report_error(int elevel, PGresult *res, bool clear, const char *sql)
{
	/* If requested, PGresult must be released before leaving this function. */
	PG_TRY();
	{
		char	   *diag_sqlstate = PQresultErrorField(res, PG_DIAG_SQLSTATE);
		char	   *message_primary = PQresultErrorField(res, PG_DIAG_MESSAGE_PRIMARY);
		char	   *message_detail = PQresultErrorField(res, PG_DIAG_MESSAGE_DETAIL);
		char	   *message_hint = PQresultErrorField(res, PG_DIAG_MESSAGE_HINT);
		char	   *message_context = PQresultErrorField(res, PG_DIAG_CONTEXT);
		int			sqlstate;

		if (diag_sqlstate)
			sqlstate = MAKE_SQLSTATE(diag_sqlstate[0],
									 diag_sqlstate[1],
									 diag_sqlstate[2],
									 diag_sqlstate[3],
									 diag_sqlstate[4]);
		else
			sqlstate = ERRCODE_CONNECTION_FAILURE;

		ereport(elevel,
				(errcode(sqlstate),
				 message_primary ? errmsg_internal("%s", message_primary) :
				 errmsg("unknown error"),
			   message_detail ? errdetail_internal("%s", message_detail) : 0,
				 message_hint ? errhint("%s", message_hint) : 0,
				 message_context ? errcontext("%s", message_context) : 0,
				 sql ? errcontext("Remote SQL command: %s", sql) : 0));
	}
	PG_CATCH();
	{
		if (clear)
			PQclear(res);
		PG_RE_THROW();
	}
	PG_END_TRY();
	if (clear)
		PQclear(res);
}

/*
 * pgfdw_xact_callback --- cleanup at main-transaction end.
 */
static void
pgfdw_xact_callback(XactEvent event, void *arg)
{
	HASH_SEQ_STATUS scan;
	ConnCacheEntry *entry;

	/* Quick exit if no connections were touched in this transaction. */
	if (!xact_got_connection)
		return;
/*
	hash_seq_init(&scan, ConnectionHash);
	while ((entry = (ConnCacheEntry *) hash_seq_search(&scan)))
	{
		PGresult   *res;
		if (entry->conn == NULL || entry->xact_depth == 0)
			continue;

		elog(DEBUG3, "closing remote transaction on connection %p",
			 entry->conn);

		switch (event)
		{
			case XACT_EVENT_PRE_COMMIT:
				do_sql_command(entry->conn, "COMMIT TRANSACTION");
				if (entry->have_prep_stmt && entry->have_error)
				{
					res = PQexec(entry->conn, "DEALLOCATE ALL");
					PQclear(res);
				}
				entry->have_prep_stmt = false;
				entry->have_error = false;
				break;
			case XACT_EVENT_PRE_PREPARE:
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("cannot prepare a transaction that modified remote tables")));
				break;
			case XACT_EVENT_COMMIT:
			case XACT_EVENT_PREPARE:
				elog(ERROR, "missed cleaning up connection during pre-commit");
				break;
			case XACT_EVENT_ABORT:
				entry->have_error = true;
				res = PQexec(entry->conn, "ABORT TRANSACTION");
				if (PQresultStatus(res) != PGRES_COMMAND_OK)
					pgfdw_report_error(WARNING, res, true,
									   "ABORT TRANSACTION");
				else
				{
					PQclear(res);
					if (entry->have_prep_stmt && entry->have_error)
					{
						res = PQexec(entry->conn, "DEALLOCATE ALL");
						PQclear(res);
					}
					entry->have_prep_stmt = false;
					entry->have_error = false;
				}
				break;
		}

		entry->xact_depth = 0;
	
		if (PQstatus(entry->conn) != CONNECTION_OK ||
			PQtransactionStatus(entry->conn) != PQTRANS_IDLE)
		{
			elog(DEBUG3, "discarding connection %p", entry->conn);
			PQfinish(entry->conn);
			entry->conn = NULL;
		}
	}

	xact_got_connection = false;
	cursor_number = 0;*/
}

/*
 * pgfdw_subxact_callback --- cleanup at subtransaction end.
 */
static void
pgfdw_subxact_callback(SubXactEvent event, SubTransactionId mySubid,
					   SubTransactionId parentSubid, void *arg)
{
	HASH_SEQ_STATUS scan;
	ConnCacheEntry *entry;
	int			curlevel;

	/* Nothing to do at subxact start, nor after commit. */
	if (!(event == SUBXACT_EVENT_PRE_COMMIT_SUB ||
		  event == SUBXACT_EVENT_ABORT_SUB))
		return;

	/* Quick exit if no connections were touched in this transaction. */
	if (!xact_got_connection)
		return;
/*
	curlevel = GetCurrentTransactionNestLevel();
	hash_seq_init(&scan, ConnectionHash);
	while ((entry = (ConnCacheEntry *) hash_seq_search(&scan)))
	{
		PGresult   *res;
		char		sql[100];
		if (entry->conn == NULL || entry->xact_depth < curlevel)
			continue;

		if (entry->xact_depth > curlevel)
			elog(ERROR, "missed cleaning up remote subtransaction at level %d",
				 entry->xact_depth);

		if (event == SUBXACT_EVENT_PRE_COMMIT_SUB)
		{
			snprintf(sql, sizeof(sql), "RELEASE SAVEPOINT s%d", curlevel);
			do_sql_command(entry->conn, sql);
		}
		else
		{
			entry->have_error = true;
			snprintf(sql, sizeof(sql),
					 "ROLLBACK TO SAVEPOINT s%d; RELEASE SAVEPOINT s%d",
					 curlevel, curlevel);
			res = PQexec(entry->conn, sql);
			if (PQresultStatus(res) != PGRES_COMMAND_OK)
				pgfdw_report_error(WARNING, res, true, sql);
			else
				PQclear(res);
		}
		entry->xact_depth--;
	}*/
}
