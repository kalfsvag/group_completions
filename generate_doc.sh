echo "Generating documentation for files in _CoqProject:"
{
 while read F  ; do
	 echo "  " $F
     coqdoc -R . "A_BPQ" -d docs $F
 done
}<tail -n+1 _CoqProject
