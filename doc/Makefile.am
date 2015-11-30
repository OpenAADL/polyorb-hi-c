###############################################################################
# $Id: Makefile.am 6950 2009-08-25 08:06:54Z hugues $
# Makefile for the PolyORB HI User's Guide
###############################################################################

C_CODE = $(srcdir)/po_hi_messages.c

H_CODE = $(srcdir)/po_hi_messages.h $(srcdir)/po_hi_time.h	\
	 $(srcdir)/po_hi_main.h $(srcdir)/po_hi_common.h	\
	 $(srcdir)/po_hi_debug.h $(srcdir)/po_hi_marshallers.h	\
	 $(srcdir)/po_hi_giop.h $(srcdir)/po_hi_gqueue.h	\
	 $(srcdir)/po_hi_transport.h $(srcdir)/po_hi_returns.h	\
	 $(srcdir)/po_hi_task.h \
	 $(srcdir)/po_hi_types.h $(srcdir)/po_hi_protected.h

SRC_CODE = $(C_CODE) $(H_CODE)

DOC_CODE = $(srcdir)/activity.c $(srcdir)/deployment.h			\
	 $(srcdir)/deployment_c.c $(srcdir)/naming.c $(srcdir)/main.c	\
	 $(srcdir)/toy_types.c $(srcdir)/toy_main.c			\
	 $(srcdir)/toy_types.h $(srcdir)/data_struct.h			\
	 $(srcdir)/node_b_activity.c $(srcdir)/marshallers.c		\
	 $(srcdir)/subprograms.c

AADL_MODELS = $(srcdir)/complex_types.aadl $(srcdir)/do_ping_spg.aadl	\
	$(srcdir)/hardware.aadl $(srcdir)/node_a_model.aadl		\
	$(srcdir)/ping.aadl $(srcdir)/port_cnx.aadl			\
	$(srcdir)/processor_binding.aadl $(srcdir)/devices.aadl		\
	$(srcdir)/protected_object_types.aadl				\
	$(srcdir)/simple_types.aadl $(srcdir)/thread_a.aadl		\
	$(srcdir)/thread_a_full.aadl $(srcdir)/scenario_sample.aadl

FIGURES = $(srcdir)/fig/ping.eps $(srcdir)/fig/ping.pdf	\
	$(srcdir)/fig/ping.png

GUIDE = polyorb-hi-c_ug

###############################################################################

SRC_CODE_TEXIFILES = ${notdir $(SRC_CODE:.h=.h.texi) $(SRC_CODE:.c=.c.texi)}
DOC_CODE_TEXIFILES = ${notdir $(DOC_CODE:.h=.h.texi) $(DOC_CODE:.c=.c.texi)}
AADL_TEXIFILES = ${notdir $(AADL_MODELS:.aadl=.texi)}

GENERATED_TEXIFILES=polyorb-hi_ug_ref.texi polyorb-hi_ug_ref.bbl	\
	polyorb-hi_ug_ref.aux

GUIDE_TEXIFILES =  $(SRC_CODE_TEXIFILES)	\
	$(DOC_CODE_TEXIFILES) $(AADL_TEXIFILES)

EXTRA_DIST= $(GUIDE_TEXIFILES) $(SRC_CODE) $(DOC_CODE) $(AADL_MODELS)	\
	$(srcdir)/CODING_GUIDELINES $(srcdir)/polyorb_hi.css		\
	$(srcdir)/conventions.texi $(srcdir)/gfdl.texi			\
	$(srcdir)/polyorb-hi_ug_ref.tex $(srcdir)/polyorb-hi_ug.bib $(FIGURES)

info_TEXINFOS =
polyorb_hi_c_ug_TEXINFOS = $(GUIDE_TEXIFILES)

SUFFIXES = .c .h .aadl .texi .sed .pdf .html

docs: $(GENERATED_TEXIFILES) $(GUIDE_TEXIFILES) $(GUIDE).html $(GUIDE).pdf

all-local: @DOC_TARGETS@

###############################################################################
# The target below are active only in developper mode. In package
# mode, once the files in doc/ have been packages, they are not
# overriden.

$(SRC_CODE):
	echo $(SRC_CODE_TEXINFOS)
	for file in $(C_CODE); do \
		cp -f $(top_srcdir)/src/`basename $${file}` $(srcdir); \
	done
	for file in $(H_CODE); do \
		cp -f $(top_srcdir)/include/`basename $${file}` $(srcdir); \
	done

$(DOC_CODE):
	for file in $(DOC_CODE); do \
	  cp -f $(srcdir)/code/`basename $${file}` $(srcdir); \
	done

$(AADL_MODELS):
	for file in $(AADL_MODELS); do \
	  cp -f $(srcdir)/model/`basename $${file}` $(srcdir); \
	done

###############################################################################
# The target below are used to build all elements of the documentation
# Targets to build a bibliography from BibTex files

polyorb-hi_ug_ref.texi: polyorb-hi_ug_ref.bbl
	@sed -e 's/~/ /g' \
	-e 's/\\[-`'\''"c^]//g' \
	-e 's/\\emdash */---/g' \
	-e 's/metapost/MetaPost/g' \
	-e 's/\\MF/Metafont/g' \
	-e 's/\\METAFONT/METAFONT/g' \
	-e 's/\\TUB/TUGboat/g' \
	-e 's/\\LaTeX/La@TeX/g' \
	-e 's/\\AMSTEX/AMS@TeX/g' \
	-e 's/\\AmSTeX/AMS@TeX/g' \
	-e 's/\\TeX/@TeX/g' \
	-e 's/\\noopsort{[^}]*}//g' \
	-e 's/[{}\]//g' \
	-e 's/@\[/{/g' \
	-e 's/@\]/}/g' \
	-e 's/@TeX/@TeX{}/g' \
	$< >$@

polyorb-hi_ug_ref.bbl: polyorb-hi_ug_ref.aux
	-TEXINPUTS="$(srcdir):.:" \
	 BIBINPUTS="$(srcdir):.:" \
	 BSTINPUTS="$(srcdir):.:" \
	   $(BIBTEX) polyorb-hi_ug_ref

polyorb-hi_ug_ref.aux: $(srcdir)/polyorb-hi_ug_ref.tex $(srcdir)/polyorb-hi_ug.bib
	rm -f polyorb-hi_ug_ref.bbl
	-TEXINPUTS="$(srcdir):.:" \
	 BIBINPUTS="$(srcdir):.:" \
	 BSTINPUTS="$(srcdir):.:" \
	   $(TEX) '\nonstopmode \input $<'

# The PolyORB HI User's Guide texi file does not provide Up links in
# @node commands, but we want to force generation of HTML
# documentation anyway.

$(GUIDE).html: $(srcdir)/$(GUIDE).texi
	$(MAKEINFO) --css-include=$(srcdir)/polyorb_hi.css --html --number-sections $(srcdir)/$(GUIDE).texi -o $(GUIDE).html
	rm -rf $(GUIDE).html/fig
	mkdir -p $(GUIDE).html/fig
	cp $(srcdir)/fig/*.png $(GUIDE).html/fig/
	INDEX_FILE="$(GUIDE).html/index.html";\
	TMP_FILE="$$INDEX_FILE.tmp"; \
	cat "$$INDEX_FILE" | sed 's/$$LastChangedDate: \([^$$]*\) \$$/Last Modified: \1/g' > "$$TMP_FILE"; \
	mv -f "$$TMP_FILE" "$$INDEX_FILE"


$(GUIDE).pdf: $(srcdir)/$(GUIDE).texi
	-$(TEXI2DVI) -o $@ --pdf $<

po_hi_doc_dir=${shell $(CYGPATH_U) '$(OCARINA_PREFIX)/share/doc/ocarina'}

install-data-local: all
	$(INSTALL) -d  $(DESTDIR)$(po_hi_doc_dir)
	$(INSTALL) -d  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html
	$(INSTALL) -d  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html/fig
	if [ -r $(builddir)/$(GUIDE).pdf ]; then \
	  $(INSTALL_DATA) $(builddir)/$(GUIDE).pdf  $(DESTDIR)$(po_hi_doc_dir); \
	  for f in $(builddir)/$(GUIDE).html/*.html; do \
            $(INSTALL_DATA) $$f  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html; \
          done; \
	  for f in $(builddir)/$(GUIDE).html/fig/*.png; do \
            $(INSTALL_DATA) $$f  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html/fig; \
          done; \
	fi
	if [ -r $(srcdir)/$(GUIDE).pdf ]; then \
	  $(INSTALL_DATA) $(srcdir)/$(GUIDE).pdf  $(DESTDIR)$(po_hi_doc_dir); \
	  for f in $(srcdir)/$(GUIDE).html/*.html; do \
            $(INSTALL_DATA) $$f  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html; \
          done; \
	  for f in $(srcdir)/$(GUIDE).html/fig/*.png; do \
            $(INSTALL_DATA) $$f  $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html/fig; \
          done; \
	fi

uninstall-local:
	rm -f $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).pdf
	rm -rf $(DESTDIR)$(po_hi_doc_dir)/$(GUIDE).html

clean-local:
	@-rm -f *.aux *.log *.dvi *.bbl *.blg *~ *.bak *.toc
	@-rm -f ${SRC_CODE} ${DOC_CODE} ${AADL_MODELS}
	@-rm -f *.sed ${GUIDE_TEXIFILES}

realclean: clean
	@-rm -f $(GUIDE).ps $(GUIDE).pdf $(GUIDE).info \
	c.sed c.sed-stamp aadl.sed aadl.sed-stamp

DISTCLEANFILES = $(GUIDE).ps $(GUIDE).pdf $(GUIDE_TEXIFILES) \
	c.sed c.sed-stamp aadl.sed aadl.sed-stamp

###############################################################################
# Texi generation from .h and .c files
#

%.h.texi: %.h $(top_srcdir)/support/gentexifile
	$(MAKE) c.sed
	$(SHELL) $(top_srcdir)/support/gentexifile $< NOGROUP
	-@${RM} genout

%.c.texi: %.c $(top_srcdir)/support/gentexifile
	$(MAKE) c.sed
	$(SHELL) $(top_srcdir)/support/gentexifile $< NOGROUP
	-@${RM} genout

%.texi: %.aadl $(top_srcdir)/support/gentexifile
	$(MAKE) aadl.sed
	$(SHELL) $(top_srcdir)/support/gentexifile $< NOGROUP
	-@${RM} genout

C_KW = void int if switch case return char float uint8_t uint16_t	\
	struct typedef enum union

c.sed: c.sed-stamp
	echo "s/\([^@]\)@\([^@]\)/\1@@\2/g"                      >  c.sed
	echo "s/{/@{/g"	  		                         >> c.sed
	echo "s/}/@}/g"			                         >> c.sed
	echo "s/-- \(.*\)$$/-- @i{\1}/"                          >> c.sed
	echo "s/\([^-][^-][^\"]*\)\"\([^\"]*\)\"/\1\"@i{\2}\"/g" >> c.sed
	echo "s/@@/@@@@/g"                                       >> c.sed
	echo "s/_@_/_@@_/g"                                      >> c.sed
	for kw in $(C_KW); do \
		echo "s/^\([^-]* \)$$kw/\1@b{$$kw}/g"            >> c.sed; \
		echo "s/^\( *\)$$kw /\1@b{$$kw} /g"              >> c.sed; \
		echo "s/^$$kw$$/@b{$$kw}/g"                      >> c.sed; \
	done

c.sed-stamp:
	touch c.sed-stamp

AADL_KW = aadlboolean aadlinteger aadlreal aadlstring access all and	\
	annex applies binding bus calls classifier connections		\
	constant data delta device end enumeration event extends flow	\
	flows group implementation in inherit initial inverse is list	\
	memory mode modes none not of or out package parameter path	\
	port private process processor properties property provides	\
	public range reference refined refines requires server set	\
	sink source subcomponents subprogram system thread to true	\
	type units value

aadl.sed: aadl.sed-stamp
	echo "s/\([^@]\)@\([^@]\)/\1@@\2/g"                      >  aadl.sed
	echo "s/@@/@@@@/g"                                       >> aadl.sed
	echo "s/_@_/_@@_/g"                                      >> aadl.sed
	echo "s/{/\@{/g"                                         >> aadl.sed
	echo "s/}/\@}/g"                                         >> aadl.sed
	echo "s/-- \(.*\)$$/-- @i{\1}/"                          >> aadl.sed
	echo "s/\([^-][^-][^\"]*\)\"\([^\"]*\)\"/\1\"@i{\2}\"/g" >> aadl.sed
	for kw in $(AADL_KW); do \
		echo "s/^\([^-]* \)$$kw/\1@b{$$kw}/g"            >> aadl.sed; \
		echo "s/^\( *\)$$kw /\1@b{$$kw} /g"              >> aadl.sed; \
		echo "s/^$$kw$$/@b{$$kw}/g"                      >> aadl.sed; \
	done

aadl.sed-stamp:
	touch aadl.sed-stamp

dist-hook: all
	-cp -r $(builddir)/$(GUIDE).html $(builddir)/$(GUIDE).pdf $(distdir)

debug-makefile:
	@echo "C_CODE = $(C_CODE)"
	@echo "H_CODE = $(H_CODE)"
	@echo "SRC_CODE = $(SRC_CODE)"
	@echo "DOC_CODE = $(DOC_CODE)"
	@echo "AADL_MODELS = $(AADL_MODELS)"
	@echo "FIGURES = $(FIGURES)"
	@echo "SRC_CODE_TEXIFILES = $(SRC_CODE_TEXIFILES)"
	@echo "DOC_CODE_TEXIFILES = $(DOC_CODE_TEXIFILES)"
	@echo "AADL_TEXIFILES = $(AADL_TEXIFILES)"
	@echo "GUIDE_TEXIFILES = $(GUIDE_TEXIFILES)"
