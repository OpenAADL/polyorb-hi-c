AUTOMAKE_OPTIONS = no-dependencies
SUBDIRS=

CPP_FILES = $(srcdir)/cheddar_schedule.cc $(srcdir)/cheddar_schedule.hh	\
$(srcdir)/cheddar_types.hh $(srcdir)/hyperperriod_config.hh

csrc = ${shell $(CYGPATH_U) '$(OCARINA_RUNTIME)/polyorb-hi-c/src'}

install-data-local:
	$(INSTALL) -d $(DESTDIR)$(csrc)
	for f in $(CPP_FILES); do $(INSTALL) -m 444 $$f $(DESTDIR)$(csrc) ; done

uninstall-local:
	rm -rf $(DESTDIR)$(csrc)

EXTRA_DIST = $(CPP_FILES) $(PYTHON_FILES)

CLEANFILES = *~

hyperperiod-cheddar:
	python get_cheddar_schedule.py
	swig -c++ -python cheddar_schedule.i
	c++ -O2 -c -fPIC -std=c++1y cheddar_schedule.cc cheddar_schedule_wrap.cxx -I/usr/include/python2.7/
	gc++ -shared cheddar_schedule.o cheddar_schedule_wrap.o -o _cheddar_schedule.so
	python parser_cheddar_et.py

recompile-cheddar: clean compile-cheddar
