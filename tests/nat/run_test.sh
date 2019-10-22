#!/usr/bin/env bash

set -o xtrace

cd nat

echo "Starting nat tests"

main_str="
main = setLocaleEncoding utf8 GHC.Base.>>
     Prelude.putStrLn (prettyProgram (program_err (denoteCoq $1)))
"

# echo $main_str

echo $main_str >> main.hs

ghc main.hs
./main > out

if cmp --silent expected.tst out
then echo "Passed!"
else echo "Failed!" \
    && diff expected.tst out \
    && exit 1
fi

cd ..
