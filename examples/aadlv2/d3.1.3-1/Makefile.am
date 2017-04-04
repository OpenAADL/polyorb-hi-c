C_FILES = $(srcdir)/toy.c
AADL_FILES = $(srcdir)/toy_example.aadl

SCENARIO_FILES = $(srcdir)/scenario_local.aadl			\
                 $(srcdir)/scenario_local_xenomai_posix.aadl	\
                 $(srcdir)/scenario_local_xenomai_native.aadl	\
                 $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = toy_example_native toy_example_xenomai	\
	toy_example_xenomai_posix toy_example_rtems
