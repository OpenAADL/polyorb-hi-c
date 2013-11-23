ACLOCAL_AMFLAGS = -I support

AUTOMAKE_OPTIONS = no-dependencies
CLEANFILES = config-stamp svn-commit*.tmp* *~
SUBDIRS = src support tools share include @DOC_DIR@
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
	$(INSTALL_DATA) $(srcdir)/ChangeLog $(DESTDIR)$(po_hi_doc_dir)/ChangeLog_polyorb_hi_c

uninstall-local:
	$(MAKE) -C examples DESTDIR="$(DESTDIR)" uninstall
	rm -f $(DESTDIR)$(po_hi_doc_dir)/ChangeLog_polyorb_hi_c

release:
	rm -rf release/
	mkdir release/
	$(MAKE) dist
	cp -f $(DIST_ARCHIVES) release/$(DIST_ARCHIVES)

# We disable checking of the distclean rule, it is a nuisance
distcleancheck:
	@:

# Conditional targets and variables for proof of the runtime
if HAS_PROOF
SRCDIR_PROOF = ./src
FILES_TO_PROVE =  po_hi_utils.c po_hi_time.c po_hi_marshallers.c \
		  po_hi_messages.c po_hi_protected.c po_hi_task.c po_hi_gqueue.c \
		  po_hi_transport.c po_hi_main.c
_FILES_TO_PROVE = $(patsubst %,$(SRCDIR_PROOF)/%,$(FILES_TO_PROVE))
CPP_PROOF_OPT = -cpp-command="$(CPP_PROOF) -C -E -I./include -I./include-proof -I./doc/code"
WP_ARGS = -wp -wp-prover alt-ergo
WP_ARGS_INTERACTIVE = -wp -wp-prover why3ide
JESSIE_ARGS = -jessie -jessie-atp alt-ergo
JESSIE_ARGS_INTERACTIVE = -jessie

proof-wp:
	$(FRAMA_C) $(WP_ARGS) $(CPP_PROOF_OPT) $(_FILES_TO_PROVE)

proof-wp-interactive:
	$(FRAMA_C) $(WP_ARGS_INTERACTIVE) $(CPP_PROOF_OPT) $(_FILES_TO_PROVE)

proof-jessie:
	$(FRAMA_C) $(JESSIE_ARGS) $(CPP_PROOF_OPT) $(_FILES_TO_PROVE)

proof-jessie-interactive:
	$(FRAMA_C) $(JESSIE_ARGS_INTERACTIVE) $(CPP_PROOF_OPT) $(_FILES_TO_PROVE)
endif
