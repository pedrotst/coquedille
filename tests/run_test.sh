#!/usr/bin/env bash

cd $1

cp ../main.hs .

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}Starting $1 tests${NC}"

main_str="
main = setLocaleEncoding utf8 GHC.Base.>>
     Prelude.putStrLn \"module $1.\" GHC.Base.>>
     Prelude.putStrLn (pretty (prettySum prettyProgram) (denoteCoq $1_syntax))
"

echo $main_str >> main.hs

ghc main.hs > /dev/null
./main > out

if cmp --silent expected out
then echo -e "${GREEN} Test Passed $1!${NC}"
else echo -e "${RED}Failed!${NC}" \
    && diff expected out \
    && exit 1
fi

cd ..
