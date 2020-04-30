#!/usr/bin/env bash

# First of all get the list of definitions in COQLIB and write to libfuns file
coqtop > libfuns <<EOF
Require Import $1.
Print $1.
EOF

# Now get the names of definitions to be extracted
# Currently it is extracting Corrolaries, Theorems, Definitions and Parameters
# At first sight extract parameters may seem weird, but we do that because oddly Coq transforms most lemmas in the
# Standard Library to Parameters. Go figure.
pcregrep -o1 -e "Lemma (.*?) :" -e "Corollary (.*?) :" -e "Theorem (.*?) :" -e "Definition (.*?) :" -e "Parameter (.*?) :" libfuns > extract_defs.txt
