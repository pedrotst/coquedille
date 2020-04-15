#!/usr/bin/env bash
#

# set -o xtrace

coqtop > libfuns <<EOF
Print $1.
EOF

params=$(pcregrep -o1 -e "Lemma (.*?) :" -e "Corollary (.*?) :" -e "Theorem (.*?) :" -e "Definition (.*?) :" -e "Parameter (.*?) :" libfuns)

make -C ..

sed -e '/LIBRARIES/a\'$'\n'"Require Import $1." Extraction.v > Extract_lib.v

for def in $params; do
    v=${def}_syntax
    echo $v
    sed -e '/COMMANDS/a\'$'\n'"Quote Recursively Definition $v := $def." Extract_lib.v > out
    sed -e '/EXTRACT/a\'$'\n'"$v" out > Extract_lib.v
    # sed -e '/LIBRARIES/a\'$'\n'"Require Import $1." Extract_lib.v > out | mv out Extract_lib.v
done

sed -e '/EXTRACT/a\'$'\n''Extraction "Extracted.hs" PrettySum PrettyProgram denoteCoq' Extract_lib.v > out
mv out Extract_lib.v

coqc -Q ../theories Coquedille Extract_lib.v

# Adds the necessary imports to the top of the file
sed -e 's/module Main where/module Extracted where/g' Extracted.hs > E.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' E.hs > Extracted.hs
sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' Extracted.hs > E.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' E.hs > Extracted.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified GHC.Base' Extracted.hs > E.hs

mv E.hs Extracted.hs

# Adds the main
echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> Extracted.hs


rm output.txt
rm -r $1

mkdir -p $1/fail

for def in $params; do
    v="${def,,}"_syntax
    sed -e "s/#ARG#/$v/g" main_gen.hs > main.hs
    ghc main.hs > /dev/null
    ./main > $1/$def.ced
    output="$(cedille $1/$def.ced 2>&1)"
    echo $output |& tee -a output.txt
    if echo $output | grep -q 'Type Checking Failed'; then
        mv $1/$def.ced $1/fail
    fi
    # cedille $1/$def.ced |& tee -a output.txt
done
