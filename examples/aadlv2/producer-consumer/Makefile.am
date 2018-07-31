C_FILES = $(srcdir)/producer-consumer.c $(srcdir)/devicesconf.c	\
	$(srcdir)/devicesconf_spw.c

AADL_FILES = $(srcdir)/producer_consumer.aadl $(srcdir)/software.aadl	\
$(srcdir)/scenario_spw.aadl

SCENARIO_FILES = $(srcdir)/scenario.aadl				\
	$(srcdir)/scenario_local.aadl					\
	$(srcdir)/scenario_loopback.aadl				\
	$(srcdir)/scenario_rtems.aadl $(srcdir)/scenario_spw2.aadl	\
	$(srcdir)/scenario_loopback_rtems.aadl

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(C_FILES)

CLEANDIRS = pc_simple_impl pc_simple_local pc_simple_rtems		\
	pc_simple_loopback pc_simple_loopback_spw pc_simple_impl_spw	\
	pc_simple_impl_spw2 pc_simple_loopback_rtems_ethernet
