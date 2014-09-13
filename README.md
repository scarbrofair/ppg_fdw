ppg_fdw
=======

	A distributed parallel query engine, based on fdw and hooks of PG.
	Our idea is to create a shared-nothing system, which is composed many pgsql servers. For these pgsql servers, one server (we call it DQ, it is short for Distributed parallel Query engine)need to install ppg_fdw (please follow the steps following), and the others store table which is sharded horizontally. (Currently, we sharding the fact tables of DW by the referenced key. How to sharding data is key to join tables. And for the demension table, we just put them on each table since they are small.)
	With ppg_fdw, DQ can run tpch SQL to access remote tables in parallel. 
	Currently, we finish the most of TPCH query instances on linux platforms. For some sql, it only access demenstion tables, it is no strong reason to accelerate with ppg_fdw. To be done later.

INSTALL:
	1, get PG src and decompress to your OS, let us assume you unzip src under dir of ~/postgres
	2, finish the steps to install PG via compiling src. Let us assume you install PG under /usr/local/PG
	3, make dir named ppg_fdw under ~/postgres/contrib/
    4, use git pull to download src of ppg_fdw under ~/postgres/contrib/ppg_fdw/
    5, compile ppg_fdw 
	6, cp ~/postgres/contrib/ppg_fdw/ppg_fdw--1.0.sql /usr/local/PG/share/postgresql/extension
    7, cp ~/postgres/contrib/ppg_fdw/ppg_fdw.control /usr/local/PG/share/postgresql/extension
    8, cp ~/postgres/contrib/ppg_fdw/ppg_fdw.so /usr/local/PG/lib/postgresql
	9, create a virtual server via ppg_fdw, run command via psql : 
		CREATE SERVER testserver1 FOREIGN DATA WRAPPER ppg_fdw options (host 'localhost', dbname 'postgres', port '5430');
	10, create user mapping for the virtual server with psql: 
		CREATE USER MAPPING FOR public SERVER testserver1 OPTIONS (user 'postgres', password '');
		NOTE: later we will this user mapping to access remote pgsql, make sure we can access these pgsql with this user mapping 
    11, add the remote pgsql servers wrappered by vertual server named testserver1 via psql:
        update pg_catalog.pg_foreign_server set srvoptions=array['host1=127.0.0.1:5430:postgres','host2=127.0.0.1:5431:postgres'] where srvname = 'testserver1';
		NOTE: above SQL adds 2 pgsql, both of them are running  on local machine, one uses 5430 port and the other uses 5431, and the database we will access is postgres 
    12  create a table on remote pgsql servers, for the case of TPCH benchmark, we create the orders table on each remote databases via psql:
		CREATE TABLE ORDERS ( O_ORDERKEY       INTEGER NOT NULL,
                           O_CUSTKEY        INTEGER NOT NULL,
                           O_ORDERSTATUS    CHAR(1) NOT NULL,
                           O_TOTALPRICE     DECIMAL(15,2) NOT NULL,
                           O_ORDERDATE      DATE NOT NULL,
                           O_ORDERPRIORITY  CHAR(15) NOT NULL,  
                           O_CLERK          CHAR(15) NOT NULL, 
                           O_SHIPPRIORITY   INTEGER NOT NULL,
                           O_COMMENT        VARCHAR(79) NOT NULL);
	 	than create a foreign table of orders on the pgsql which later will call ppg_fdw to access remote pgsql in parallel:
		CREATE FOREIGN TABLE ORDERS  ( O_ORDERKEY       INTEGER NOT NULL,
                           O_CUSTKEY        INTEGER NOT NULL,
                           O_ORDERSTATUS    CHAR(1) NOT NULL,
                           O_TOTALPRICE     DECIMAL(15,2) NOT NULL,
                           O_ORDERDATE      DATE NOT NULL,
                           O_ORDERPRIORITY  CHAR(15) NOT NULL,  
                           O_CLERK          CHAR(15) NOT NULL, 
                           O_SHIPPRIORITY   INTEGER NOT NULL,
                           O_COMMENT        VARCHAR(79) NOT NULL) SERVER testserver1;
       NOTE the difference of above 2 SQL.
       ppg_fdw provides script named tpch_example_setup.sql, which will create the foreign tables for TPCH. You can check it.

