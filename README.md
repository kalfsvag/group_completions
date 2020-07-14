# Approaching the Barratt-Priddy-Quillen theorem in HoTT.
Coq code for PhD thesis "Approaching the Barratt-Priddy-Quillen theorem in homotopy type theory."

Code in folder 1type_completion is written by Niels van der Weide and Dan Frumin, and is copied from https://github.com/nmvdw/groupoids, with only minor changes by me.


To compile:
coq_makefile -f _CoqProject -o Makefile
make

To generate documentation:
coqdoc -R . "A_BPQ" -d doc [list of files]
