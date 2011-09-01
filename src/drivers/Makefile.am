AUTOMAKE_OPTIONS = no-dependencies

SUBDIRS=configuration

C_FILES =   $(srcdir)/po_hi_driver_linux_serial.c        \
            $(srcdir)/po_hi_driver_leon_serial.c         \
            $(srcdir)/po_hi_driver_leon_eth.c            \
            $(srcdir)/po_hi_driver_sockets.c             \
            $(srcdir)/po_hi_driver_rtems_ne2000.c        \
            $(srcdir)/po_hi_driver_rasta_spacewire.c     \
            $(srcdir)/po_hi_driver_rasta_common.c        \
            $(srcdir)/po_hi_driver_exarm.c               \
            $(srcdir)/po_hi_driver_usbbrick_spacewire.c  \
            $(srcdir)/po_hi_driver_serial_common.c       \
            $(srcdir)/po_hi_driver_keyboard.c            \
            $(srcdir)/po_hi_driver_exarm_ni_6071e_analog.c            \
            $(srcdir)/po_hi_driver_exarm_ni_6071e_digital.c            \
            $(srcdir)/po_hi_driver_rasta_1553.c          \
            $(srcdir)/po_hi_driver_xc4v_fpga.c          \
            $(srcdir)/po_hi_driver_rasta_1553_brmlib.c   \
            $(srcdir)/po_hi_driver_rasta_serial.c

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src/drivers'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(C_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(C_FILES)

CLEANFILES = *~
