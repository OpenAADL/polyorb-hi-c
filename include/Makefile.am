AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS=drivers monitoring simulator

EXTRA_DIST = $(srcdir)/po_hi_common.h \
             $(srcdir)/po_hi_debug.h \
             $(srcdir)/po_hi_marshallers.h \
             $(srcdir)/po_hi_messages.h \
             $(srcdir)/po_hi_protected.h \
             $(srcdir)/po_hi_returns.h \
             $(srcdir)/po_hi_gqueue.h \
             $(srcdir)/po_hi_monitor.h \
             $(srcdir)/po_hi_lua.h \
             $(srcdir)/po_hi_storage.h \
             $(srcdir)/po_hi_giop.h \
             $(srcdir)/po_hi_utils.h \
             $(srcdir)/po_hi_task.h \
             $(srcdir)/po_hi_time.h \
             $(srcdir)/po_hi_types.h \
             $(srcdir)/po_hi_main.h \
             $(srcdir)/po_hi_simulink.h \
             $(srcdir)/po_hi_transport.h

CLEANFILES = *~

hsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/include'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(hsrc)
	for f in $(EXTRA_DIST) $(CONFIG_HEADER); do \
	  $(INSTALL) -m 444 $$f $(DESTDIR)$(hsrc) ; \
	done

uninstall-local:
	rm -rf $(DESTDIR)$(hsrc)
