#!/usr/bin/env bash

# Modify here to add new test cases
declare -a TESTCASES=("nat" "list" "option" "vector" "le" "iff" "asgn" "refl1" "lnil"
"lcons" "nileqnil" "zeroneqS" "mul")

# Uncomment this line to see each command being run
# set -o xtrace

NC='\033[0m'
YELLOW='\033[1;33m'

echo -e "${YELLOW}Extracting test cases to Haskell...${NC}"
coqc -Q ../theories Coquedille Extraction.v

# Adds the necessary imports to the top of the file
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Bits' main.hs > m.hs
sed -e '/import qualified Prelude/a\'$'\n''import GHC.IO.Encoding' m.hs > main.hs
sed -e '/import qualified Prelude/a\'$'\n''import qualified Data.Char' main.hs > m.hs

# GHC.Base.Any is poly-kinded, which leaves the kind variables in the extracted
# monad stack's type synonym uninferrable. Every value of that type goes through
# unsafeCoerce, so pinning Any to a single kind is safe.
sed -e 's/^type Any = GHC.Base.Any$/type Any = ()/' m.hs > main.hs

rm -f m.hs

# Adds the main
echo "
program_err :: Option Program0 -> Program0
program_err None = Nil
program_err (Some p) = p
" >> main.hs

# Run each test case
for tst in ${TESTCASES[@]}; do
    ./run_test.sh $tst
done

