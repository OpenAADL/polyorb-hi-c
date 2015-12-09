AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS=drivers monitoring simulator python

C_FILES = $(srcdir)/po_hi_task.c $(srcdir)/po_hi_main.c			\
             $(srcdir)/po_hi_marshallers.c $(srcdir)/po_hi_messages.c	\
             $(srcdir)/po_hi_monitor.c $(srcdir)/po_hi_gqueue.c		\
             $(srcdir)/po_hi_giop.c $(srcdir)/po_hi_lua.c		\
             $(srcdir)/po_hi_protected.c $(srcdir)/po_hi_transport.c	\
             $(srcdir)/po_hi_storage.c $(srcdir)/po_hi_types.c		\
             $(srcdir)/po_hi_utils.c $(srcdir)/po_hi_simulink.c		\
             $(srcdir)/po_hi_gprof_rtems_leon.c				\
             $(srcdir)/po_hi_time.c

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(C_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(C_FILES)

CLEANFILES = *~
