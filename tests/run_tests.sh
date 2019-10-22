#!/usr/bin/env bash

coqc -Q ../theories Coquedille -Q ../coq-haskell/src Hask Extraction.v

# Adds the necessary imports to the top of the file
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' m.hs > main.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' main.hs > m.hs

mv m.hs main.hs

# Adds the main
echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> main.hs

# main = Prelude.putStrLn (prettyProgram (program_err (denoteCoq nat_syntax)))" >> main.hs

# Compile and run
# ghc main.hs
# ./main > nat.ced

cp main.hs nat
cp main.hs list
cp main.hs option

./nat/run_test.sh nat_syntax
./list/run_test.sh list_syntax
./option/run_test.sh option_syntax
