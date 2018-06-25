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

lcov -c -i -d ./some_types_stdint_impl/node_a/ -o .coverage.base_node_a
lcov -c -d ./some_types_stdint_impl/node_a/ -o .coverage.run_node_a
lcov -d ./some_types_stdint_impl/node_a/ -a .coverage.base_node_a -a .coverage.run_node_a -o .coverage.total

lcov -c -i -d ./some_types_stdint_impl/node_b -o .coverage.base_node_b
lcov -c -d ./some_types_stdint_impl/node_b -o .coverage.run_node_b
lcov -d ./some_types_stdint_impl/node_b -a .coverage.base_node_a -a .coverage.run_node_a -a .coverage.base_node_b -a .coverage.run_node_b -o .coverage.total

genhtml --no-branch-coverage -o $OUTPUT_DIR .coverage.total
#genhtml --no-branch-coverage -o b_$OUTPUT_DIR .coverage.total_b
