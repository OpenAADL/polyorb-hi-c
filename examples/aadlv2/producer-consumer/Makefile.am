C_FILES = $(srcdir)/producer-consumer.c  $(srcdir)/devicesconf.c

AADL_FILES = $(srcdir)/producer_consumer.aadl $(srcdir)/software.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl				\
	$(srcdir)/scenario_local.aadl $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = pc_simple_impl pc_simple_local pc_simple_rtems
