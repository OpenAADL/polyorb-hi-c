C_FILES = $(srcdir)/flight-mgmt.c
AADL_FILES = $(srcdir)/flt_mgmt.aadl $(srcdir)/software.aadl

SCENARIO_FILES = $(srcdir)/scenario_local.aadl				\
	$(srcdir)/scenario_local_xenomai.aadl				\
	$(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = flight_mgmt_native flight_mgmt_xenomai flight_mgmt_local	\
	flight_mgmt_rtems
