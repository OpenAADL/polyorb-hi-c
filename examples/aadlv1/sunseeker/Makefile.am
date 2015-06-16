C_FILES =  \
	$(srcdir)/sunseekercontroller.c \
	$(srcdir)/sunseekerplant.c

AADL_FILES = \
           $(srcdir)/sunseeker.aadl \
           $(srcdir)/sunseeker_local.aadl

SCENARIO_FILES = $(srcdir)/scenario_local.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = sunseekercontrolsystem_type_local sunseekercontrolsystem_type_dist
