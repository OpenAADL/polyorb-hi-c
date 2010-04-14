#!/bin/sh

# Build script for all examples
#  -c : Cleaning up all files
# default: Building for native target

top_dir=$PWD

if [ "$1" = "-c" ];
    then 
    CMD="make clean";
    echo "*** Cleaning up files ***"
else
    CMD="make";   
    echo "*** Building for default target ***"
fi

for dir in \
    $top_dir/examples/rma/ \
    $top_dir/examples/ping/ \
    $top_dir/examples/producer-consumer/ \
    $top_dir/examples/flight-mgmt/ \
    $top_dir/examples/some-types-stdint/ \
    $top_dir/examples/some-types/ \
    $top_dir/examples/d3.1.3-1/ \
    $top_dir/examples/sunseeker/
  do
  
  cd $dir
  echo Processing: $dir

  TEMPORARY_FILE=temp.$$
  $CMD > $TEMPORARY_FILE 2>&1
  a=$?
  if [ $a != 0 ];
      then 
      cat $TEMPORARY_FILE
      echo `pwd` ": make failed : exit status = " $a
      echo `pwd` ": FAILED"
  else
      echo `pwd` ": PASSED"
      if [ "$1" != "-c" ]; then
	       rm -f $TEMPORARY_FILE
      fi
  fi

  cd $top_dir
done

if [ "$1" = "-c" ]; then 
  echo "Clean $top_dir"
  cd $top_dir && $CMD 1>/dev/null 2>&1
fi

