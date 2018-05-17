#!/bin/sh
# Test fusion at model-level
#
# currently simply tests that the model resulting from analysis is
# analysable by Ocarina

TMP_FILE="post_fusion.aadl"
IN_FILE="pre_fusion.aadl"
RESULT_FILE="results.log"
LOG_FILE="ocarina_execution.log"
LOAD_FILE_LIST="load_file_list"
WORKDIR=$PWD
AADL_VERSION="aadlv2"
SINGLE_TEST="single_fusion.sh"

for test in `ls . | grep test_`
  do

  cd ${WORKDIR}/${test}
  rm -f ${TMP_FILE}
  
  echo "" >> ${WORKDIR}/${LOG_FILE}

  # Create a single file containing all relevant AADL data for input

  echo "Concat all input files"
  echo "Concat all input files" >> ${WORKDIR}/${LOG_FILE}
  ocarina -${AADL_VERSION} -o ${IN_FILE} -t < ${WORKDIR}/${LOAD_FILE_LIST} >> ${WORKDIR}/${LOG_FILE};

  echo "Fusion files"
  echo "Fusion files" >> ${WORKDIR}/${LOG_FILE}
  ocarina -${AADL_VERSION} -o ${TMP_FILE} -t < ${WORKDIR}/${SINGLE_TEST} >> ${WORKDIR}/${LOG_FILE};
  
  if [ -e ${TMP_FILE} ] 
      then
      ocarina -${AADL_VERSION} -i ${TMP_FILE} 1> ${RESULT_FILE};
  else
      echo "Error : ${test} failed !" >> ${WORKDIR}/${LOG_FILE}
      cat ${WORKDIR}/${LOG_FILE}
      exit 1;	
  fi
  if [ -e ${RESULT_FILE} ] 
      then
      if [ -s ${RESULT_FILE} ]
	  then
	  echo "Error : ${test} failed !" >> ${WORKDIR}/${LOG_FILE}
	  cat ${WORKDIR}/${LOG_FILE};
	  rm ${RESULT_FILE}
	  exit 1;
      else
	  rm ${RESULT_FILE}
      fi
  else
      echo "Error : ${test} failed !" >> ${WORKDIR}/${LOG_FILE}
      cat ${WORKDIR}/${LOG_FILE};
      exit 1;
  fi

  echo "test ${test} passed successfully";
  echo "------------------"
  echo ""
  rm -f ${LOG_FILE};
  cd  ${WORKDIR};
done

echo "    -------------  ";
echo "All fusion tests were successful";
exit 0;
