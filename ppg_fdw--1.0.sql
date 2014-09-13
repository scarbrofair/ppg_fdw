/* cp ./ppg_fdw--1.0.sql /usr/local/PG93/share/postgresql/extension   */
/* cp ./ppg_fdw.control  /usr/local/PG93/share/postgresql/extension/ */
/*cp ./ppg_fdw.so /usr/local/PG93/lib/postgresql/   */
/*

*/
-- complain if script is sourced in psql, rather than via CREATE EXTENSION
\echo Use "CREATE EXTENSION ppg_fdw" to load this file. \quit

CREATE FUNCTION ppg_fdw_handler()
RETURNS fdw_handler
AS 'MODULE_PATHNAME'
LANGUAGE C STRICT;

CREATE FUNCTION ppg_fdw_validator(text[], oid)
RETURNS void
AS 'MODULE_PATHNAME'
LANGUAGE C STRICT;

CREATE FOREIGN DATA WRAPPER ppg_fdw
  HANDLER ppg_fdw_handler
  VALIDATOR ppg_fdw_validator;

