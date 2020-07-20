echo "Compiling files in _CoqProject:"
while read F  ; do
	echo "  " $F
    hoqc -R . "A_BPQ" $F
done <_CoqProject
