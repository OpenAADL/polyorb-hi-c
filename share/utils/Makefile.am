EXTRA_DIST=$(srcdir)/x86-rtems-boot.img

CLEANFILES = *~

utilssrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/utils'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(utilssrc)
	for f in $(EXTRA_DIST); do $(INSTALL) -m 444 $$f $(DESTDIR)$(utilssrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(utilssrc)


