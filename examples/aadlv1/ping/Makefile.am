C_FILES = $(srcdir)/ping.c
AADL_FILES = \
	$(srcdir)/ping-local.aadl  \
	$(srcdir)/software.aadl  \
	$(srcdir)/ping.aadl

SCENARIO_FILES = \
	$(srcdir)/scenario-local.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = ping_local ping_impl
