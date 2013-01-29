AUTOMAKE_OPTIONS = no-dependencies

LIBS_FILES = $(srcdir)/liblua-linux64.a $(srcdir)/liblua-linux32.a	\
               $(srcdir)/liblua-leon.a $(srcdir)/liblua-leon-rtems48.a

libdest = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/libs'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(libdest)/linux32
	$(INSTALL) -d $(DESTDIR)$(libdest)/linux64
	$(INSTALL) -d $(DESTDIR)$(libdest)/leon-rtems4.8
	$(INSTALL) -d $(DESTDIR)$(libdest)/leon-rtems4.11
	$(INSTALL) -m 444 $(srcdir)/liblua-leon-rtems48.a $(DESTDIR)$(libdest)/leon-rtems4.8/liblua.a
	$(INSTALL) -m 444 $(srcdir)/liblua-linux32.a $(DESTDIR)$(libdest)/linux32/liblua.a
	$(INSTALL) -m 444 $(srcdir)/liblua-linux64.a $(DESTDIR)$(libdest)/linux64/liblua.a

uninstall-local:
	rm -f $(DESTDIR)$(libdest)/linux64/liblua.a
	rm -f $(DESTDIR)$(libdest)/linux32/liblua.a
	rm -f $(DESTDIR)$(libdest)/leon-rtems4.8/liblua.a
	rm -f $(DESTDIR)$(libdest)/leon-rtems4.11/liblua.a

EXTRA_DIST = $(LIBS_FILES)

CLEANFILES = *~
