#!/bin/sh

EXEC_FILE_PATH=./@PROGRAM_NAME@

for i in "$@"
do
case $i in
    --output-dir-name=*)
    OUTPUT_DIR="${i#*=}" #ONLY NAME OF DIR
    shift # past argument=value
    ;;
    --check=*)
    CHECK_OPTION="${i#*=}" #call:callgrind or cache:cachegrind
    shift # past argument=value
    ;;
    *)
            # unknown option
    ;;
esac
done


if [ -z "$OUTPUT_DIR" ]; then
  OUTPUT_DIR=./prof_output
else
  OUTPUT_DIR=./$OUTPUT_DIR
fi

if (! test -d $OUTPUT_DIR )
then
  echo "Missing path: $OUTPUT_DIR. Creating directory..."
  mkdir $OUTPUT_DIR
fi

if [ "$CHECK_OPTION" = "cache" ]; then
  
valgrind --tool=cachegrind --log-file=valgrind_callgrind.log --cachegrind-out-file=$OUTPUT_DIR/cachegrind.out $EXEC_FILE_PATH
cg_annotate --show=Dr,Dw $OUTPUT_DIR/cachegrind.out > $OUTPUT_DIR/cachegrind_an.txt

#To tell callgrind_annotate to dump out the xxx.c file and to annotate each line with the number of instrustions it took:
#$ callgrind_annotate {callgrind.out path}/callgrind.out {xxx.c path}/xxx.c

elif [ "$CHECK_OPTION" = "call" ]; then

valgrind --dsymutil=yes --tool=callgrind --log-file=valgrind_callgrind.log --callgrind-out-file=$OUTPUT_DIR/callgrind.out $EXEC_FILE_PATH
callgrind_annotate $OUTPUT_DIR/callgrind.out > $OUTPUT_DIR/callgrind_an.txt

elif [ "$CHECK_OPTION" = "massif" ]; then

valgrind --tool=massif --stacks=yes --log-file=valgrind_callgrind.log --massif-out-file=$OUTPUT_DIR/massif.out $EXEC_FILE_PATH
ms_print $OUTPUT_DIR/massif.out > $OUTPUT_DIR/massif_an.txt

elif [ "$CHECK_OPTION" = "mem" ]; then

valgrind --tool=memcheck --leak-check=full --log-file=valgrind_memcheck.log $EXEC_FILE_PATH
valgrind --tool=memcheck --leak-check=full --xml=yes --xml-file=valgrind_memcheck.xml $EXEC_FILE_PATH 
#valgrind --tool=memcheck --leak-check=full --log-file=valgrind_memcheck.log $EXEC_FILE_PATH  2>  $OUTPUT_DIR/memcheck_an.txt
#valgrind --tool=memcheck --leak-check=full $EXEC_FILE_PATH  2>  $OUTPUT_DIR/memcheck_an.txt

else

echo "Unknown option"

fi




