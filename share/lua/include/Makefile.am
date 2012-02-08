AUTOMAKE_OPTIONS = no-dependencies

H_FILES =   $(srcdir)/lua.h           \
            $(srcdir)/lua.hpp           \
            $(srcdir)/lualib.h           \
            $(srcdir)/luaconf.h           \
	         $(srcdir)/lauxlib.h

hsrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/include'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(hsrc)
	$(INSTALL) -d $(DESTDIR)$(hsrc)/lua/
	for f in $(H_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(hsrc)/lua ; done

uninstall-local:
	rm -rf $(DESTDIR)$(hsrc)/lua

EXTRA_DIST = $(H_FILES)

CLEANFILES = *~
