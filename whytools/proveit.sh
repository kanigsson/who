#!/bin/bash
set -x
if [ -z "$TIMEOUT" ] ; then
  TIMEOUT=5
fi
if [ -z "$CORES" ] ; then
  CORES=5
fi
CAT=`date +%F+%X`
proofmgr -add-bench -c $CAT $*
PROVERS=`proofmgr -show-provers | grep "\[.*\]" | sed -e "s/.*\[.\(.*\)\].*/\1/"`
for i in $PROVERS ; do
  proofmgr -run -i $i -c $CAT -timeout $TIMEOUT -cores $CORES
done

