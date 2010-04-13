#!/bin/bash

set -x
TIMEOUT=5
while getopts 't:' OPTION
do
  case $OPTION in
    t) TIMEOUT=$OPTARG ;;
    ?) exit 2;;
  esac
done

CAT=`date +%F+%X`
proofmgr -add-bench -c $CAT $*
proofmgr -run -i 1 -c $CAT -cores 5 -timeout $TIMEOUT
proofmgr -run -i 2 -c $CAT -cores 2 -timeout $TIMEOUT
proofmgr -run -i 3 -c $CAT -cores 3 -timeout $TIMEOUT
proofmgr -run -i 4 -c $CAT -cores 2 -timeout $TIMEOUT
proofmgr -run -i 5 -c $CAT -cores 5 -timeout $TIMEOUT

