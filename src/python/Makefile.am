AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS=

C_FILES = $(srcdir)/po_hi_c_python.i $(srcdir)/trace_manager.i

PYTHON_FILES = $(srcdir)/cheddar.py $(srcdir)/parser_cheddar_et.py	\
   $(srcdir)/cheddar_script.py $(srcdir)/parser_cheddar_system.py	\
   $(srcdir)/get_cheddar_schedule.py $(srcdir)/trace_manager.py		\
   $(srcdir)/lauch_demo.py

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(C_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done
	for f in $(PYTHON_FILES); do $(INSTALL) -m 755 $$f $(DESTDIR)$(OCARINA_PREFIX)/bin ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(C_FILES)

CLEANFILES = *~
