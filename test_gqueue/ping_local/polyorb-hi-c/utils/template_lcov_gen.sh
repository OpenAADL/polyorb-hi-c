#!/bin/sh
for i in "$@"
do
case $i in
    --output-dir-name=*)
    OUTPUT_DIR="${i#*=}" #ONLY NAME OF DIR
    shift # past argument=value
    ;;
    *)
            # unknown option
    ;;
esac
done

if [ -z "$OUTPUT_DIR" ]; then
  OUTPUT_DIR=./gcov_output
else
  OUTPUT_DIR=./$OUTPUT_DIR
fi

if (! test -d $OUTPUT_DIR )
then
  echo "Missing path: $OUTPUT_DIR. Creating directory..."
  mkdir $OUTPUT_DIR
fi

lcov -c -i -d $PWD -o .coverage.base
lcov -c -d $PWD -o .coverage.run
lcov -d $PWD -a .coverage.base -a .coverage.run -o .coverage.total
genhtml --no-branch-coverage -o $OUTPUT_DIR .coverage.total
rm -f .coverage.base .coverage.run .coverage.total
