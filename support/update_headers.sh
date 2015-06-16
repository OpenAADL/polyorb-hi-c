#!/bin/sh

# $Id: update_headers.sh 5393 2008-01-18 12:20:54Z zalila $

# This script has to ve invoked from the PolyORB-HI main directory

headers_po_hi="support/headers_po_hi"

usage () {
    cat <<EOF
Usage: ${0} [OPTIONS]
Options:
        No option:
           Update the Copyright headers only for the newly added files and
           the modified files (using SVN).

        [all]
           Updates the Copyright headers of all files.
EOF
}

if ! test -x ${headers_po_hi}; then
    make -C support headers-po_hi
fi;

if test $# = 0 ; then
    echo "Updating headers for changed and new files"

    changed_files=`git status -s | grep "^\ M" | grep '\.\(\([ch]\)\)' | awk '{print $NF}'`
    added_files=`git status -s | grep "^[A]" | grep '\.\(\([ch]\)\)' | awk '{print $NF}'`

    # For changed files, update the header

    for i in ${changed_files}; do
	${headers_po_hi} ${i}
    done

    # For Added files, create a new header

    for i in ${added_files}; do
	${headers_po_hi} -noh ${i} > /dev/null 2>&1
	${headers_po_hi} ${i}
    done
else
    if test x${1} = xall ; then
	echo "Updating headers for all files"

	find . -name "*.c" -exec ${headers_po_hi} $1 '{}' \;
	find . -name "*.h" -exec ${headers_po_hi} $1 '{}' \;
    else
	usage 1>&2
	exit 1
    fi
fi

exit 0
