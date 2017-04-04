C_FILES = $(srcdir)/some-types.c $(srcdir)/devicesconf.c

AADL_FILES = $(srcdir)/some_types.aadl $(srcdir)/software.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl				\
	$(srcdir)/scenario_local.aadl $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = some_types_impl some_types_local some_types_rtems
