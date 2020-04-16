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

# Deletes line that simply refuses to work
del="eqb_spec0 :: T0 -> T0 -> Reflect\neqb_spec0 =\n eqb_spec"

sed -e "/^eqb_spec0 :: T0 -> T0 -> Reflect/d" m.hs > main.hs
sed -e "/neqb_spec0 =$/d" main.hs > m.hs
sed -e "/^  eqb_spec$/d" m.hs > main.hs

mv m.hs main.hs

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

