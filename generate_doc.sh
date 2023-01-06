echo "Generating documentation for files in _CoqProject:"
{
	read
	while read F  ; do
		echo "  " $F
		coqdoc -R . "GCTT" -d docs $F #add --latex to generate tex files
	done 
} < _CoqProject
