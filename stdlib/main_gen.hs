import Extracted

import qualified Prelude
import GHC.Base
import qualified Data.Char
import GHC.IO.Encoding
import qualified Data.Bits

main = setLocaleEncoding utf8 >>
     Prelude.putStrLn "module test." >>
     Prelude.putStrLn (pretty (prettySum prettyProgram) (denoteCoq #ARG#))
