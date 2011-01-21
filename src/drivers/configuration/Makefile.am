AUTOMAKE_OPTIONS = no-dependencies

C_FILES =   $(srcdir)/1553.c       \
            $(srcdir)/ip.c         \
            $(srcdir)/serial.c     \
            $(srcdir)/spacewire.c

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src/drivers/configuration'}

$(srcdir)/1553.c:
	asn1.exe -c -typePrefix __po_hi_c_ 1553.asn
	mv 1553.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/spacewire.c:
	asn1.exe -c -typePrefix __po_hi_c_ spacewire.asn
	mv spacewire.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/ip.c:
	asn1.exe -c -typePrefix __po_hi_c_ ip.asn
	mv ip.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/serial.c:
	asn1.exe -c -typePrefix __po_hi_c_ serial.asn
	mv serial.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

regenerate:
	rm -f $(C_FILES)
	for v in $(C_FILES); do $(MAKE) $$v ; done

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(C_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(C_FILES)

CLEANFILES = *~ $(C_FILES)
