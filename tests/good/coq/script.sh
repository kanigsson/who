basename=`basename $1 .who`
../../../main.native --coq $1
coqc -I ../../../coq_files $basename\_who.v
