echo "Compiling files in _CoqProject:"
{
	read
	while read F  ; do
		echo "  " $F
		hoqc -R . "GCTT" $F
	done
} < _CoqProject
