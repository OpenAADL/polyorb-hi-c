C_FILES = $(srcdir)/hello.c
AADL_FILES = $(srcdir)/rma.aadl \
             $(srcdir)/rma-xenomai-posix.aadl \
             $(srcdir)/rma-compcert.aadl \
             $(srcdir)/rma-bench.aadl \
             $(srcdir)/rma-xenomai-native.aadl


SCENARIO_FILES = $(srcdir)/scenario.aadl			\
                  $(srcdir)/scenario-compcert.aadl		\
                  $(srcdir)/scenario-xenomai-native.aadl	\
                  $(srcdir)/scenario-xenomai-posix.aadl		\
                  $(srcdir)/scenario-rtems.aadl

# remove target, linux specific
#                  $(srcdir)/scenario-bench.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = rma_impl rma_rtems

