#!/usr/bin/env bash

coqc -Q ../theories Coquedille -Q ../coq-haskell/src Hask Extraction.v

# sed -e '/CLIENTSCRIPT="foo"/a\'$'\n''CLIENTSCRIPT2="hello"' file

sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' m.hs > main.hs
rm m.hs

echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p

main = Prelude.putStrLn (prettyProgram (program_err (denoteCoq nat_syntax)))" >> main.hs
