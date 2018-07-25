C_FILES = $(srcdir)/functions.c
AADL_FILES = $(srcdir)/latency.aadl $(srcdir)/latencyevent.aadl	\
	$(srcdir)/latencyevent-original.aadl			\
	$(srcdir)/latency-original.aadl

SCENARIO_FILES = \
                  $(srcdir)/scenario_local.aadl	\
                  $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = topsystem_local topsystem_rtems
