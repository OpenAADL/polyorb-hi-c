EXTRA_DIST=$(srcdir)/x86-rtems-boot.img $(srcdir)/gumstix-uboot.bin	\
           $(srcdir)/template_sonar-project.properties			\
           $(srcdir)/template_lcov_gen.sh				\
           $(srcdir)/template_prof_gen.sh $(srcdir)/xpath

CLEANFILES = *~

utilssrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/utils'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(utilssrc)
	for f in $(EXTRA_DIST); do $(INSTALL) -m 444 $$f $(DESTDIR)$(utilssrc) ; done
	$(INSTALL) -m 755 $(srcdir)/xpath $(DESTDIR)$(utilssrc)

uninstall-local:
	rm -rf $(DESTDIR)$(utilssrc)
