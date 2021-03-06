#!/usr/bin/env bash

make -C ..
sed "s/THISISPROGRAM/$1/g;s/THISISLIBRARY/$2/g" Extraction.v > out.v
coqc -Q ../theories Coquedille out.v

# Adds the necessary imports to the top of the file
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' m.hs > main.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' main.hs > m.hs sed -e '/import qualified Prelude/a\'$'\n''import qualified GHC.Base' m.hs > main.hs

# mv m.hs main.hs

# Adds the main
echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> main.hs

main_str="
main = setLocaleEncoding utf8 GHC.Base.>>
     Prelude.putStrLn \"module test.\" GHC.Base.>>
     Prelude.putStrLn (pretty (prettySum prettyProgram) (denoteCoq p))
"

echo $main_str >> main.hs
mkdir -p $2

ghc main.hs
./main > $2/$1.ced
cedille $2/$1.ced
