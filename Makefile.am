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
FRAMA_C_LIBC_SHARE = $(shell $(FRAMA_C) -print-share-path)/libc
FRAMA_C_OPT = -pp-annot
CPP_PROOF_OPT = -cpp-extra-args="-I./include-proof -I./doc/code"
_WP_RTE = $(if $(NO_RTE),,-wp-rte)
WP_ARGS = -wp $(_WP_RTE) -wp-timeout 60 -wp-split -wp-prover
WHY_PROVER = alt-ergo
PROVER_OPTIONS =
_WP_FILTER = $(if $(WP_FILTER),-wp-fct $(WP_FILTER),)
_WP_VERBOSE = $(if $(WP_VERBOSE),-wp-print -wp-out proof-obligations,)

HEADERS_FOR_PROOF = include-proof/time.h

include-proof/%.h: $(FRAMA_C_LIBC_SHARE)/%.h
	cp $< $@; /bin/sed -n -i -e '/__END_DECLS/r ./include-proof-templates/$(notdir $<)' -e 1x -e '2,$${x;p}' -e '$${x;p}' $@

proof-wp: $(HEADERS_FOR_PROOF)
	$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) alt-ergo $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE)

proof-wp-report: $(HEADERS_FOR_PROOF)
	$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) alt-ergo $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE) -then -report

proof-wp-interactive: $(HEADERS_FOR_PROOF)
	$(FRAMA_C_INTERACTIVE) $(FRAMA_C_OPT) $(WP_ARGS) alt-ergo $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE)

proof-wp-pretty-print: $(HEADERS_FOR_PROOF)
	$(foreach file,$(FILES_TO_PROVE),$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) alt-ergo $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) src/$(file) > report/report_$(subst .c,.txt,$(file)) ;)
	cd report; ./format-cu.py $(FILES_TO_PROVE)

proof-why: $(HEADERS_FOR_PROOF)
	$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) "why3:$(WHY_PROVER)" $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE)

proof-why-report: $(HEADERS_FOR_PROOF)
	$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) "why3:$(WHY_PROVER)" $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE) -then -report

proof-why-interactive: $(HEADERS_FOR_PROOF)
	$(FRAMA_C) $(FRAMA_C_OPT) $(WP_ARGS) why3ide $(_WP_VERBOSE) $(CPP_PROOF_OPT) $(_WP_FILTER) $(PROVER_OPTIONS) $(_FILES_TO_PROVE)
endif
