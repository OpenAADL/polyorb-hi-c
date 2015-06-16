AUTOMAKE_OPTIONS = no-dependencies
EXTRA_DIST = $(srcdir)/asn1crt.h \
             $(srcdir)/1553.h \
             $(srcdir)/ip.h \
             $(srcdir)/serial.h\
             $(srcdir)/spacewire.h

hsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/include/drivers/configuration'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(hsrc)
	for f in $(EXTRA_DIST); do \
	  $(INSTALL) -m 444 $$f $(DESTDIR)$(hsrc) ; \
	done

uninstall-local:
	rm -rf $(DESTDIR)$(hsrc)


CLEANFILES = *~

