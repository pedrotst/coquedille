#!/usr/bin/env bash
#

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

sed -e '/EXTRACT/a\'$'\n''Extraction "main.hs" PrettySum PrettyProgram denoteCoq' Extract_lib.v > out
mv out Extract_lib.v

coqc -Q ../theories Coquedille Extract_lib.v

# Adds the necessary imports to the top of the file
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' m.hs > main.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified GHC.Base' m.hs > main.hs

# mv m.hs main.hs

# Adds the main
echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> main.hs

mkdir -p $1

main_str="
main = setLocaleEncoding utf8 GHC.Base.>>
     Prelude.putStrLn \"module test.\" GHC.Base.>>
     Prelude.putStrLn (pretty (prettySum prettyProgram) (denoteCoq p))
"

echo $main_str >> main.hs

ghc main.hs

for def in $params; do
    ./main > $1/$def.ced
    cedille $1/$def.ced
done
