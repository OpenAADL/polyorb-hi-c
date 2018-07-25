C_FILES = $(srcdir)/ptest.c $(srcdir)/whetstone.c
AADL_FILES = $(srcdir)/ptest.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl	\
                  $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = ptest_impl ptest_rtems_impl
