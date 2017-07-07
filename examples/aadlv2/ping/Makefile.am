C_FILES = $(srcdir)/ping.c $(srcdir)/ping.h  $(srcdir)/devicesconf.c
AADL_FILES = $(srcdir)/ping-local.aadl					\
	$(srcdir)/ping-local-xenomai-native.aadl			\
	$(srcdir)/ping-local-xenomai-posix.aadl				\
	$(srcdir)/ping-xenomai-posix.aadl $(srcdir)/software.aadl	\
	$(srcdir)/ping.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl				\
	$(srcdir)/scenario-local-xenomai-posix.aadl			\
	$(srcdir)/scenario-xenomai-posix.aadl				\
	$(srcdir)/scenario-local-xenomai-native.aadl			\
	$(srcdir)/scenario-local.aadl $(srcdir)/scenario-rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = ping_local ping_impl ping_ima ping_federated ping_rtems

