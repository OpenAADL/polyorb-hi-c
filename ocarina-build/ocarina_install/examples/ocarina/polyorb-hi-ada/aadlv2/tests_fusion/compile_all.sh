#!/bin/sh
# Test fusion at code-level

WORKDIR=$PWD
IN_FILE=post_fusion

for test in `ls . | grep test_`
  do
  cd ${WORKDIR}/${test}

   echo "generate code for $test :"
   echo ""

   ocarina -aadlv2 -g polyorb_hi_ada $IN_FILE.aadl

   if [ $? != 0 ] 
       then
       echo "code generation failed"
       exit 1
   fi

   cd ping_erc32/node_a
   make

   if [ $? != 0 ] 
       then
       echo "code compilation failed"
       exit 1
   fi

   cd ../..

  cd  ${WORKDIR};

  echo "    -----  ";
  echo ""
done

echo "    -------------  ";
echo "All fusion compilations were successful";
exit 0;
