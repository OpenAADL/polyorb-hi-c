EXTRA_DIST=$(builddir)/Makefile.common $(srcdir)/Makefile.leon3-xm3	\
	     $(srcdir)/Makefile.leon3-scoc3				\
	     $(srcdir)/Makefile.leon3-xtratum				\
	     $(srcdir)/Makefile.leon.rtems				\
	     $(srcdir)/Makefile.leon.rtems_posix			\
	     $(srcdir)/Makefile.compcert $(srcdir)/Makefile.bench	\
	     $(srcdir)/Makefile.linux32					\
	     $(srcdir)/Makefile.linux32_dll				\
	     $(srcdir)/Makefile.linux32-xenomai-native			\
	     $(srcdir)/Makefile.linux32-xenomai-posix			\
	     $(srcdir)/Makefile.linux64					\
	     $(srcdir)/Makefile.linux64_dll $(srcdir)/Makefile.win32	\
	     $(srcdir)/Makefile.x86.linuxtaste				\
	     $(srcdir)/Makefile.template $(srcdir)/Makefile.freertos	\
	     $(srcdir)/Makefile.air

CLEANFILES = *~

makesrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/make'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(makesrc)
	for f in $(EXTRA_DIST) Makefile.native; do $(INSTALL) -m 444 $$f $(DESTDIR)$(makesrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(makesrc)
