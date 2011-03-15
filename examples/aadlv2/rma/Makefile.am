C_FILES = $(srcdir)/hello.c
AADL_FILES = $(srcdir)/rma.aadl \
             $(srcdir)/rma-xenomai-posix.aadl \
             $(srcdir)/rma-xenomai-native.aadl


SCENARIO_FILES =  $(srcdir)/scenario.aadl \
                  $(srcdir)/scenario-xenomai-native.aadl \
                  $(srcdir)/scenario-xenomai-posix.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILE) $(C_FILES)

CLEANDIRS = rma_impl
