AUTOMAKE_OPTIONS = no-dependencies
CLEANFILES = config-stamp svn-commit*.tmp* *~
SUBDIRS = src support doc tools share include
DIST_SUBDIRS = $(SUBDIRS) examples

check-local:: examples

examples:: install
	$(MAKE) -C examples build-all

run-examples::
	$(MAKE) -C examples check-all

clean-examples::
	$(MAKE) -C examples clean

distclean-examples::
	$(MAKE) -C examples distclean

po_hi_doc_dir = ${shell $(CYGPATH_U) '$(OCARINA_PREFIX)/share/doc/ocarina'}

install-data-local:
	$(MAKE) -C examples DESTDIR="$(DESTDIR)" install
	$(INSTALL_DATA) $(srcdir)/ChangeLog $(DESTDIR)$(po_hi_doc_dir)/ChangeLog_polyorb_hi_c

uninstall-local:
	$(MAKE) -C examples DESTDIR="$(DESTDIR)" uninstall
	rm -f $(DESTDIR)$(po_hi_doc_dir)/ChangeLog_polyorb_hi_c
