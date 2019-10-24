Require Import Ascii.
Require Import String.

Require Import MetaCoq.Template.All.
Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

Require Coq.extraction.Extraction.
Extraction Language Haskell.


(* Controlling extraction of specific types *)
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]. (* enumeration types *)
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]
.
(* types that require parameters on their constructors *)
(* type, [constructors], recursor *)
Extract Inductive nat => "GHC.Base.Int" ["0" "(\ x -> x Prelude.+ 1)"]
  "(\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))".

Extract Constant plus             => "(Prelude.+)".
Extract Constant mult             => "(Prelude.*)".
Extract Constant PeanoNat.Nat.eqb => "( Prelude.== )".

(* Properly extract the unicode tokens *)
Extract Constant TkStar    => "['★']".
Extract Constant TkArrow   => "['➔']".
Extract Constant TkPi      => "['Π']".
Extract Constant TkAll     => "['∀']".
Extract Constant TkTpDot   => "['·']".

Extract Inductive ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr ( (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+ (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+ (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+ (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+ (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+ (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+ (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+ (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".
Extract Inductive string => "Prelude.String" [ "([])" "(:)" ].
Extract Inlined Constant String.string_dec => "(Prelude.==)".
Extract Inlined Constant String.eqb => "(Prelude.==)".


(* Adds Everything we will test here *)
Quote Recursively Definition nat_syntax := nat.
Quote Recursively Definition list_syntax := list.
Quote Recursively Definition option_syntax := option.
Quote Recursively Definition vector_syntax := Vectors.Vector.t.
(* We are finally ready to extract the programs we want *)
Extraction "main.hs" PrettyProgram denoteCoq
           nat_syntax list_syntax option_syntax vector_syntax.
