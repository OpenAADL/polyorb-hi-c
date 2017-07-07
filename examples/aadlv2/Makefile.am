SUBDIRS = d3.1.3-1 ping rma sunseeker producer-consumer some-types	\
	some-types-stdint flight-mgmt import monitor lua cpp		\
	packet-store file-store

SAMPLE_DIR = ${shell $(CYGPATH_U) '$(OCARINA_PREFIX)/examples/ocarina/polyorb-hi-c/aadlv2'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(SAMPLE_DIR)
	$(INSTALL_DATA) $(srcdir)/README $(DESTDIR)$(SAMPLE_DIR)

uninstall-local:
	rm -rf $(DESTDIR)$(SAMPLE_DIR)

build-all:
	for dir in $(SUBDIRS); do \
		($(MAKE) -C $${dir} build-all) || exit 1;  \
	done

check-all:
	for dir in $(SUBDIRS); do \
                ($(MAKE) -C $${dir} check-all) || exit 1;  \
        done

