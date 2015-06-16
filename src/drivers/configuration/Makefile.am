AUTOMAKE_OPTIONS = no-dependencies

C_FILES =   $(srcdir)/1553.c       \
            $(srcdir)/ip.c         \
            $(srcdir)/serial.c     \
            $(srcdir)/spacewire.c

ASN_FILES = $(srcdir)/1553.asn       \
            $(srcdir)/ip.asn         \
            $(srcdir)/serial.asn     \
            $(srcdir)/spacewire.asn


csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src/drivers/configuration'}

$(srcdir)/1553.c:
	asn1.exe -c -typePrefix __po_hi_c_ 1553.asn
	sed -e 's/Mil\_1553\_Conf\_T/mil\_1553\_conf\_t/g' 1553.h > 1553new.h
	mv 1553new.h 1553.h
	echo "#if (defined (__PO_HI_NEED_DRIVER_1553_RASTA))\n" > 1553new.c
	sed -e 's/Mil\_1553\_Conf\_T/mil\_1553\_conf\_t/g' 1553.c >> 1553new.c
	echo "\n#endif" >> 1553new.c
	mv 1553new.c 1553.c
	mv 1553.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/spacewire.c:
	asn1.exe -c -typePrefix __po_hi_c_ spacewire.asn
	sed -e 's/Spacewire\_Conf\_T/spacewire\_conf\_t/g' spacewire.h > spacewirenew.h
	mv spacewirenew.h spacewire.h
	echo "#if (defined (__PO_HI_NEED_DRIVER_SPACEWIRE_RASTA))\n" > spacewirenew.c
	sed -e 's/Spacewire\_Conf\_T/spacewire\_conf\_t/g' spacewire.c >> spacewirenew.c
	echo "\n#endif" >> spacewirenew.c
	mv spacewirenew.c spacewire.c
	mv spacewire.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

$(srcdir)/ip.c:
	asn1.exe -c -typePrefix __po_hi_c_ ip.asn
	mv asn1crt.h ../../../include/drivers/configuration/
	sed -e 's/IP\_Conf\_T/ip\_conf\_t/g' ip.h > ipnew.h
	mv ipnew.h ip.h
	echo "#if (defined (__PO_HI_NEED_DRIVER_SOCKETS) || defined (__PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS))\n" > ipnew.c
	sed -e 's/IP\_Conf\_T/ip\_conf\_t/g' ip.c >> ipnew.c
	echo "\n#endif" >> ipnew.c
	mv ipnew.c ip.c
	mv ip.h ../../../include/drivers/configuration/

$(srcdir)/serial.c:
	asn1.exe -c -typePrefix __po_hi_c_ serial.asn
	sed -e 's/Serial\_Conf\_T/serial\_conf\_t/g' serial.h > serialnew.h
	mv serialnew.h serial.h
	echo "#if (defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER) || defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER) || defined (__PO_HI_NEED_DRIVER_SERIAL_RASTA) || defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER) || defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER))\n" > serialnew.c
	sed -e 's/Serial\_Conf\_T/serial\_conf\_t/g' serial.c >> serialnew.c
	echo "\n#endif" >> serialnew.c
	mv serialnew.c serial.c
	mv serial.h ../../../include/drivers/configuration/
	mv asn1crt.h ../../../include/drivers/configuration/

regenerate:
	rm -f $(C_FILES)
	for v in $(C_FILES); do $(MAKE) $$v ; done

install-data-local: $(C_FILES) $(ASN_FILES)
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(C_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done
	for f in $(ASN_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(C_FILES) $(ASN_FILES)

CLEANFILES = *~
