#!/usr/bin/env bash
#

# USAGE: ./run_lib2.sh COQLIB
# where COQLIB is the full name of the library to be extracted

# set -o xtrace


# First of all get the list of definitions in COQLIB and write to libfuns file
coqtop > libfuns <<EOF
Require Import $1.
Print $1.
EOF

# Now get the names of definitions to be extracted
# Currently it is extracting Corrolaries, Theorems, Definitions and Parameters
# At first sight extract parameters may seem weird, but we do that because oddly Coq transforms most lemmas in the
# Standard Library to Parameters. Go figure.
params=$(pcregrep -o1 -e "Lemma (.*?) :" -e "Corollary (.*?) :" -e "Theorem (.*?) :" -e "Definition (.*?) :" -e "Parameter (.*?) :" libfuns)

make -C ..

for def in $params; do
    v=${def}_syntax
    echo $v
    sed -e '/LIBRARIES/a\'$'\n'"Require Import $1." Extraction.v > Extract_lib.v
    sed -e "s/#LIBRARY/$1/g" Extract_lib.v > out
    sed -e "s/#DEF/$def/g" out > Extract_lib.v
    sed -e '/COMMANDS/a\'$'\n'"Quote Recursively Definition $v := $def." Extract_lib.v > out

    sed -e '/EXTRACT/a\'$'\n'"$v" out > Extract_lib.v
    sed -e '/EXTRACT/a\'$'\n''Extraction "Extracted.hs" PrettySum PrettyProgram denoteCoq' Extract_lib.v > out
    mv out Extract_lib.v

    coqc -Q ../theories Coquedille Extract_lib.v

    # Adds the necessary imports to the top of the file
    sed -e 's/module Main where/module Extracted where/g' Extracted.hs > E.hs
    sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' E.hs > Extracted.hs
    sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' Extracted.hs > E.hs
    sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' E.hs > Extracted.hs
    sed -e '/import qualified Prelude/a\'$'\n''import qualified GHC.Base' Extracted.hs > E.hs


    # For some reason Coq extracts eqb_spec0 with an incorrect type coercion
    sed -e "/^eqb_spec0 :: T0 -> T0 -> Reflect/d" E.hs > Extracted.hs
    sed -e "/eqb_spec0 =$/d" Extracted.hs > E.hs
    sed -e "/^  eqb_spec$/d" E.hs > Extracted.hs

    # mv E.hs Extracted.hs

    # Do we need this anymore?
    echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> Extracted.hs


    # rm output.txt
    # rm -r $1

    mkdir -p $1/fail

    # 1) Change the name of the definition we will use at main.hs
    # Haskell function defininitions cannot start with an uppercase, so we
    # change the first letter of the name here with this comma notation
    v="${def,}"_syntax
    sed -e "s/#ARG#/$v/g" main_gen.hs > main.hs
    # 2) Compile the main
    ghc main.hs > /dev/null
    # 3) Run the main and write the output to the correct folder
    ./main > $1/$def.ced
    # 4) Run cedille to the output of main and write it to a file
    output="$(cedille $1/$def.ced 2>&1)"
    echo $output |& tee -a output.txt
    # 5) Check if the file from 4 contains a failure
    if echo $output | grep -q 'Type Checking Failed'; then
        mv $1/$def.ced $1/fail
    fi
done
