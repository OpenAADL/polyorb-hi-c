AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS=

EXTRA_DIST =$(srcdir)/trace_manager.h

CLEANFILES = *~

hsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/include'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(hsrc)
	for f in $(EXTRA_DIST) $(CONFIG_HEADER); do \
	  $(INSTALL) -m 444 $$f $(DESTDIR)$(hsrc) ; \
	done

uninstall-local:
	rm -rf $(DESTDIR)$(hsrc)
