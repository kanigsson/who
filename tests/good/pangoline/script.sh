basename=`basename $1 .who`
../../../main.native $1 &&
pangoline --namecheck-only $basename\_who.pge
