AUTOMAKE_OPTIONS = no-dependencies
EXTRA_DIST = $(srcdir)/po_hi_driver_linux_serial.h       \
             $(srcdir)/po_hi_driver_exarm.h              \
             $(srcdir)/po_hi_driver_exarm_ni_6071e_analog.h              \
             $(srcdir)/po_hi_driver_exarm_ni_6071e_digital.h              \
             $(srcdir)/po_hi_driver_rasta_spacewire.h    \
             $(srcdir)/po_hi_driver_rasta_1553.h         \
             $(srcdir)/po_hi_driver_rasta_1553_brmlib.h  \
             $(srcdir)/po_hi_driver_xc4v_fpga.h          \
             $(srcdir)/po_hi_driver_rasta_serial.h       \
             $(srcdir)/po_hi_driver_rasta_common.h       \
             $(srcdir)/po_hi_driver_sockets.h            \
             $(srcdir)/po_hi_driver_keyboard.h           \
             $(srcdir)/po_hi_driver_sockets_common.h     \
             $(srcdir)/po_hi_driver_sockets_asn1.h       \
             $(srcdir)/po_hi_rtems_utils.h

CLEANFILES = *~

hsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/include/drivers'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(hsrc)
	for f in $(EXTRA_DIST); do \
	  $(INSTALL) -m 444 $$f $(DESTDIR)$(hsrc) ; \
	done

uninstall-local:
	rm -rf $(DESTDIR)$(hsrc)


