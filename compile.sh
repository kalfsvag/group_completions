echo "Compiling files in _CoqProject:"
while read F  ; do
	echo "  " $F
    hoqc -R . "GCTT" $F
done <_CoqProject
