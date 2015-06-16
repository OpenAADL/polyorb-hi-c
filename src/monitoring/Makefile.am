AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS= cheddar_scheduling

CPP_FILES = $(srcdir)/trace_manager.cc		\
	$(srcdir)/remote_configuration.cc

PYTHON_FILES = $(srcdir)/make_cheddar.py	\
	$(srcdir)/parse_cheddar_xml.py

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(CPP_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done
	for f in $(PYTHON_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(CPP_FILES) $(PYTHON_FILES)

CLEANFILES = *~
