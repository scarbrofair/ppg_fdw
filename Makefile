# contrib/postgres_fdw/Makefile

MODULE_big = ppg_fdw
OBJS = ppg_planner.o ppg_subselect.o postgres_fdw.o option.o deparse.o connection.o util.o

PG_CPPFLAGS = -I$(libpq_srcdir)
SHLIB_LINK = $(libpq) -lpthread
SHLIB_PREREQS = submake-libpq

EXTENSION = ppg_fdw
DATA = ppg_fdw--1.0.sql

REGRESS = ppg_fdw

# the db name is hard-coded in the tests
override USE_MODULE_DB =

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/ppg_fdw
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif
