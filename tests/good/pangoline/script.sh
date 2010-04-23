basename=`basename $1 .who`
../../../main.native --clear --noprelude $1 &&
pangoline --noprelude --pprint --namecheck-only $basename\_who.pge
