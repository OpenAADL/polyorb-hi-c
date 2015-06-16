SUBDIRS = aadlv1 aadlv2
EXTRA_DIST = Makefile.common

SAMPLE_DIR = ${shell $(CYGPATH_U) '$(OCARINA_PREFIX)/examples/ocarina/polyorb-hi-c'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(SAMPLE_DIR)

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
