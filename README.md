# Approaching the Barratt-Priddy-Quillen theorem in HoTT.
Coq code for PhD thesis "Approaching the Barratt-Priddy-Quillen theorem in homotopy type theory."

Code in folder cquot is written by Niels van der Weide and Dan Frumin, and is copied from https://github.com/nmvdw/groupoids, with only minor changes by me.

To compile:
run `.compile.sh`

Alternatively:
Add
  `-R . "A_BPQ" COQC = hoqc COQDEP = hoqdep`
as the first line in _CoqProject, then run
1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`

To generate documentation:
'coqdoc -R . "A_BPQ" -d docs [list of files]'

Known to compile with the HoTT library version [1e2173240f85d2a3f8bbc60ae90db96d0617431e](https://github.com/HoTT/HoTT/commit/1e2173240f85d2a3f8bbc60ae90db96d0617431e).
