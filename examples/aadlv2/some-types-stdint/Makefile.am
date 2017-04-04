C_FILES = $(srcdir)/some-types-stdint.c  $(srcdir)/devicesconf.c

AADL_FILES = $(srcdir)/some_types_stdint.aadl $(srcdir)/software.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl $(srcdir)/scenario_local.aadl	\
	$(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = some_types_stdint_impl some_types_local_rtems	\
	some_types_local_impl
