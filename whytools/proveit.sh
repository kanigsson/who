#!/bin/bash

set -x
TIMEOUT=5
CORES=5
while getopts 't:c:' OPTION
do
  case $OPTION in
    t) TIMEOUT=$OPTARG ;;
    c) CORES=$OPTARG ;;
    ?) exit 2;;
  esac
done

CAT=`date +%F+%X`
proofmgr -add-bench -c $CAT $*
PROVERS=`proofmgr -show-provers | grep "\[.*\]" | sed -e "s/.*\[.\(.*\)\].*/\1/"`
for i in $PROVERS ; do
  proofmgr -run -i $i -cores $CORES -c $CAT -timeout $TIMEOUT
done

