#/bin/sh

find . -name "core.*" -exec rm -f '{}' \;
find . -name "*~" -exec rm -f '{}' \;
find . -name "*.bak" -exec rm -f '{}' \;
find . -name "*.metrix" -exec rm -f '{}' \;
find . -name "temp.*" -exec rm -f '{}' \;
find . -name "svn-commit.*" -exec rm -f '{}' \;

./support/build.sh -c 
cd support; make clean; cd ..
make distclean
rm -fr autom4te.cache/ aclocal.m4 config.h config.h.in config.log \
       configure config.status \
       support/missing \
       support/install-sh \
       support/config.guess \
       support/clean \
       support/config.sub 
