C_FILES = $(srcdir)/ping.c $(srcdir)/ping.h  $(srcdir)/devicesconf.c
AADL_FILES = $(srcdir)/software.aadl $(srcdir)/ping.aadl	\
	$(srcdir)/ping-local.aadl

SCENARIO_FILES = \
	$(srcdir)/scenario.aadl

# $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = ping_impl
