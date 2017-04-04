C_FILES =  \
	$(srcdir)/sunseekercontroller.c \
	$(srcdir)/sunseekerplant.c  $(srcdir)/devicesconf.c

AADL_FILES = \
           $(srcdir)/sunseeker.aadl \
           $(srcdir)/sunseeker_dist.aadl \
           $(srcdir)/sunseeker_local.aadl

SCENARIO_FILES = $(srcdir)/scenario_local.aadl			\
	$(srcdir)/scenario_dist.aadl $(srcdir)/scenario_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = sunseekercontrolsystem_type_local	\
	sunseekercontrolsystem_type_dist	\
	sunseekercontrolsystem_type_rtems
