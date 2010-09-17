#!/bin/bash
PROOFMGR="proofmgr-nogui"
set -x
if [ -z "$TIMEOUT" ] ; then
  TIMEOUT=5
fi
if [ -z "$CORES" ] ; then
  CORES=5
fi
CAT=`date +%F+%X`
$PROOFMGR -add-bench -c $CAT $*
PROVERS=`$PROOFMGR -show-provers | grep "\[.*\]" | sed -e "s/.*\[.\(.*\)\].*/\1/"`
for i in $PROVERS ; do
  $PROOFMGR -run -i $i -c $CAT -timeout $TIMEOUT -cores $CORES
done

