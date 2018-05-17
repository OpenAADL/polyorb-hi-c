#!/bin/sh
# Test fusion at code-level and analyze the resulting binaries
#
# Use boundt_sparc, tpo_gen and ocarina

WORKDIR=$PWD

rm -f ${LOG_FILE};

for test in `ls . | grep test_`
  do
  cd ${WORKDIR}/${test}

  echo ${test}

  echo ""

  # Create a single file containing all relevant AADL data for input

  echo "generate and analyze original model"

  ../analyze.sh pre_fusion

  echo "generate and analyze fusioned model"

  ../analyze.sh post_fusion

  cd  ${WORKDIR};

  echo "    -----  ";
done

echo "    -------------  ";
echo "All analyzes are finished";
exit 0;
