AC_PREREQ(2.60)
AC_INIT(PolyORB-HI/C, 2017.x)
AC_CONFIG_SRCDIR(src)
AC_CONFIG_AUX_DIR(support)

AC_CANONICAL_HOST
AM_INIT_AUTOMAKE([1.9 tar-pax] foreign)
AM_CONFIG_HEADER(include/po_hi_config.h)

AH_TOP([
#ifndef HAVE_PO_HI_CONFIG_H
#define HAVE_PO_HI_CONFIG_H
])

AC_PROG_CC
AC_LANG_C
AC_PROG_INSTALL

## We need some external programs in order to build
## PolyORB-HI-C and its documentation.

AC_CHECK_PROG(MV, mv, mv)
AC_CHECK_PROG(RM, rm, rm)
AC_CHECK_PROG(CP, cp, cp)
AC_CHECK_PROG(GREP, grep, grep)
AC_CHECK_PROG(CHMOD, chmod, chmod)
AC_CHECK_PROG(TEX, tex, tex)
AC_CHECK_PROG(BIBTEX, bibtex, bibtex)

AC_HEADER_STDBOOL

AC_CHECK_SIZEOF(char)
AC_CHECK_SIZEOF(float)
AC_CHECK_SIZEOF(double)
AC_CHECK_SIZEOF(long double)
AC_CHECK_SIZEOF(int)
AC_CHECK_SIZEOF(unsigned int)
AC_CHECK_SIZEOF(long int)
AC_CHECK_SIZEOF(unsigned long int)
AC_CHECK_SIZEOF(short int)
AC_CHECK_SIZEOF(unsigned short int)

AC_CHECK_FUNC(clock_gettime, AC_DEFINE(HAVE_CLOCK_GETTIME, [], [Check if the system supports the clock_gettime function]),)

AC_C_BIGENDIAN

AH_BOTTOM([
#endif /* ! HAVE_PO_HI_CONFIG_H */
])

##################################################
# Set CFLAGS and LDFLAGS for the native platform #
##################################################

CFLAGS="-Wall -O"
NATIVE_CFLAGS=""
NATIVE_LDFLAGS=""
SIMULINK_LDFLAGS=""

case ${host_os} in
	*darwin*)
		NATIVE_CFLAGS="${NATIVE_CFLAGS} -DPOSIX -D_XOPEN_SOURCE"
		NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lpthread"
		;;
	*solaris*10*)
		NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lrt"
		;;
	*freebsd*)
		NATIVE_CFLAGS="${NATIVE_CFLAGS} -DPOSIX -D_GNU_SOURCE"
		NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lpthread -lrt"
		SIMULINK_LDFLAGS="-lm"
		;;
	*cygwin*)
		NATIVE_CFLAGS="${NATIVE_CFLAGS} -D_GNU_SOURCE"
		NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lpthread -lwsock32"
		SIMULINK_LDFLAGS="-lm"
		;;
	*)
		NATIVE_CFLAGS="${NATIVE_CFLAGS} -DPOSIX -D_POSIX_SOURCE -D_GNU_SOURCE"
		NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lpthread -lrt"
		SIMULINK_LDFLAGS="-lm"
		;;
esac

AC_CHECK_LIB(socket, socket, [NATIVE_LDFLAGS="${NATIVE_LDFLAGS} -lsocket"])

AC_SUBST(NATIVE_CFLAGS)
AC_SUBST(NATIVE_LDFLAGS)
AC_SUBST(SIMULINK_LDFLAGS)

##########################################
# Check for Ocarina
##########################################

AM_PATH_OCARINA(1.1, ,AC_MSG_ERROR([Ocarina 1.1 or later is not installed on your system]))

AC_ARG_ENABLE(debug,
  [  --enable-debug[=level] specify debugging level.
                            Values are:
                             * critical - runtime errors that will imply a failure
                             * warning  - runtime errors that do not crash the system
                             * debug    - useful for debugging purpose
                             * info     - ALL informations about the system],
  [ case ${enableval} in
	info)
      AC_DEFINE_UNQUOTED(__PO_HI_DEBUG_LEVEL, 12, "Debug level - show ALL potential informations.")
		;;
	debug)
      AC_DEFINE_UNQUOTED(__PO_HI_DEBUG_LEVEL, 10, "Warning - information that can show errors but are not so important")
		;;
	warning)
      AC_DEFINE_UNQUOTED(__PO_HI_DEBUG_LEVEL, 6, "Warning - Errors that will imply a minor error at run-tine")
		;;
	critical)
      AC_DEFINE_UNQUOTED(__PO_HI_DEBUG_LEVEL, 4, "Critical - Errors that will imply a fault or a crash")
		;;
	*)
      AC_DEFINE_UNQUOTED(__PO_HI_DEBUG_LEVEL, 0, "None - Do not print anything")
		;;
   esac])

AC_ARG_ENABLE(giop,
  [  --enable-giop           Use the GIOP protocol],
  [ AC_DEFINE([__PO_HI_USE_GIOP], [], ["Enable the GIOP protocol"])])

HAS_LUA_=

AC_ARG_ENABLE(lua,
  [  --enable-lua            Use the LUA script engine],
  [ AC_DEFINE([__PO_HI_USE_LUA], [], ["Enable the LUA script engine"])
if [[ "$enableval" = "yes" ]]; then
        HAS_LUA_=true
fi])

AC_SUBST(HAS_LUA_)
AM_CONDITIONAL(HAS_LUA, [test ! "x$HAS_LUA_" = "x"])

############################################
# Set the value corresponding to cygpath -u
############################################

if test x"$CYGPATH_W" = x"echo"; then
   CYGPATH_U="echo"
else
   CYGPATH_U="cygpath -u"
fi
AC_SUBST(CYGPATH_U)

##########################################
# Build documentation
##########################################

AC_CHECK_PROGS(TEXI2HTML, texi2html)

DOC_TARGETS=

AC_ARG_ENABLE(doc,
[  --enable-doc            Build documentation [default=no]],
[if [[ "$enableval" = "yes" ]]; then
        DOC_TARGETS=docs
fi],
[])

AC_SUBST(DOC_TARGETS)

###############################################################
# Use of BOOST
###############################################################

#BOOST_REQUIRE([1.55.0],[echo])
AX_BOOST_BASE([1.55.0], [], [])

###############################################################
# Force the installation prefix to be equal to the Ocarina one
###############################################################

prefix='$(OCARINA_PREFIX)'

##########################################
# Output generated files
##########################################

dnl Important! One file per line, nothing before
dnl or after except whitespace! This section
dnl may, one day, be edited automatically to remove
dnl some entries.

AC_OUTPUT([
	Makefile
	doc/Makefile
	src/Makefile
	src/drivers/Makefile
	src/drivers/configuration/Makefile
        src/monitoring/Makefile
        src/monitoring/cheddar_scheduling/Makefile
        src/python/Makefile
        src/simulator/Makefile
	include/Makefile
	include/drivers/Makefile
	include/drivers/configuration/Makefile
        include/monitoring/Makefile
        include/simulator/Makefile
	examples/Makefile
	examples/aadlv1/Makefile
	examples/aadlv1/d3.1.3-1/Makefile
	examples/aadlv1/ping/Makefile
	examples/aadlv1/flight-mgmt/Makefile
	examples/aadlv1/rma/Makefile
	examples/aadlv1/sunseeker/Makefile
	examples/aadlv2/Makefile
	examples/aadlv2/cpp/Makefile
	examples/aadlv2/d3.1.3-1/Makefile
	examples/aadlv2/import/Makefile
	examples/aadlv2/ping/Makefile
	examples/aadlv2/lua/Makefile
	examples/aadlv2/producer-consumer/Makefile
	examples/aadlv2/flight-mgmt/Makefile
	examples/aadlv2/monitor/Makefile
	examples/aadlv2/packet-store/Makefile
	examples/aadlv2/file-store/Makefile
	examples/aadlv2/rma/Makefile
	examples/aadlv2/some-types/Makefile
	examples/aadlv2/some-types-stdint/Makefile
	examples/aadlv2/sunseeker/Makefile
	tools/Makefile
	tools/check-symbols/Makefile
	tools/check-symbols/examples/Makefile
	tools/check-symbols/examples/malloc/Makefile
	tools/check-symbols/examples/strings/Makefile
	tools/check-symbols/src/Makefile
	share/Makefile
	share/lua/Makefile
	share/lua/libs/Makefile
	share/lua/include/Makefile
	share/cheddar/Makefile
	share/models/Makefile
	share/ocarina/Makefile
	share/tsim/Makefile
	share/make/Makefile
	share/utils/Makefile
	share/make/Makefile.common
	share/make/Makefile.native
	share/config/Makefile
	share/config/spif-rtems/Makefile
	share/config/leon-rtems/Makefile
	share/config/nds-rtems/Makefile
	share/config/gumstix-rtems/Makefile
	support/Makefile
])
