EXTRA_DIST=$(srcdir)/Makefile.common \
           $(srcdir)/Makefile.arm.dslinux \
			  $(srcdir)/Makefile.arm.n770 \
			  $(srcdir)/Makefile.leon.ork \
			  $(srcdir)/Makefile.leon.rtems \
			  $(srcdir)/Makefile.spif.rtems \
           $(srcdir)/Makefile.template

CLEANFILES = *~

makesrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/make'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(makesrc)
	for f in $(EXTRA_DIST) Makefile.native; do $(INSTALL) -m 444 $$f $(DESTDIR)$(makesrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(makesrc)


