EXTRA_DIST=$(srcdir)/config.c \
	$(srcdir)/po_hi_rtemsconfig.h

CLEANFILES = *~

configsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/config/leon-rtems'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(configsrc)
	for f in $(EXTRA_DIST); do $(INSTALL) -m 444 $$f $(DESTDIR)$(configsrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(configsrc)
