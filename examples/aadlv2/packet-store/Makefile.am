C_FILES = $(srcdir)/pinger.c $(srcdir)/pingme.c $(srcdir)/ping.h  $(srcdir)/devicesconf.c
AADL_FILES = \
	$(srcdir)/software.aadl  \
	$(srcdir)/ping.aadl

SCENARIO_FILES = \
	$(srcdir)/scenario.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = ping_impl
