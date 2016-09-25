ACLOCAL_AMFLAGS = -I support

AUTOMAKE_OPTIONS = no-dependencies
CLEANFILES = config-stamp svn-commit*.tmp* *~
SUBDIRS = src support tools share include doc
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

generate-driver-configuration::
	$(MAKE) -C src/drivers/configuration regenerate

po_hi_doc_dir = ${shell $(CYGPATH_U) '$(OCARINA_PREFIX)/share/doc/ocarina'}

install-data-local:
	$(MAKE) -C examples DESTDIR="$(DESTDIR)" install
	$(INSTALL) -d $(DESTDIR)$(po_hi_doc_dir)

uninstall-local:
	$(MAKE) -C examples DESTDIR="$(DESTDIR)" uninstall

release:
	rm -rf release/
	mkdir release/
	$(MAKE) dist
	cp -f $(DIST_ARCHIVES) release/$(DIST_ARCHIVES)

# We disable checking of the distclean rule, it is a nuisance
distcleancheck:
	@:
