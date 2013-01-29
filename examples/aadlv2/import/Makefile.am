C_FILES= $(srcdir)/ping.ads \
	$(srcdir)/ping.adb $(srcdir)/import.c \
	$(srcdir)/devicesconf.c \
	$(srcdir)/import_cpp.cpp

AADL_FILES = $(srcdir)/ping.aadl $(srcdir)/software.aadl
SCENARIO_FILE=$(srcdir)/scenario.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILE) $(C_FILES)

CLEANDIRS=ping_native
