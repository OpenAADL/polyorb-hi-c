AUTOMAKE_OPTIONS = no-dependencies

C_FILES =   $(srcdir)/1553.c       \
            $(srcdir)/ip.c         \
            $(srcdir)/serial.c     \
            $(srcdir)/spacewire.c

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src/drivers/configuration'}

$(srcdir)/1553.c:
	asn1.exe -c -typePrefix __po_hi_c_ 1553.asn
	sed -e 's/Mil\_1553\_Conf\_T/mil\_1553\_conf\_t/g' 1553.h > 1553new.h
	mv 1553new.h 1553.h
	sed -e 's/Mil\_1553\_Conf\_T/mil\_1553\_conf\_t/g' 1553.c > 1553new.c
	mv 1553new.c 1553.c
	mv 1553.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/spacewire.c:
	asn1.exe -c -typePrefix __po_hi_c_ spacewire.asn
	sed -e 's/Spacewire\_Conf\_T/spacewire\_conf\_t/g' spacewire.h > spacewirenew.h
	mv spacewirenew.h spacewire.h
	sed -e 's/Spacewire\_Conf\_T/spacewire\_conf\_t/g' spacewire.c > spacewirenew.c
	mv spacewirenew.c spacewire.c
	mv spacewire.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/ip.c:
	asn1.exe -c -typePrefix __po_hi_c_ ip.asn
	mv asn1crt.h ../../../include/drivers/configuration/
	sed -e 's/IP\_Conf\_T/ip\_conf\_t/g' ip.h > ipnew.h
	mv ipnew.h ip.h
	sed -e 's/IP\_Conf\_T/ip\_conf\_t/g' ip.c > ipnew.c
	mv ipnew.c ip.c
	mv ip.h ../../../include/drivers/configuration/

$(srcdir)/serial.c:
	asn1.exe -c -typePrefix __po_hi_c_ serial.asn
	sed -e 's/Serial\_Conf\_T/serial\_conf\_t/g' serial.h > serialnew.h
	mv serialnew.h serial.h
	sed -e 's/Serial\_Conf\_T/serial\_conf\_t/g' serial.c > serialnew.c
	mv serialnew.c serial.c
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
