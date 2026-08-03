From MetaRocq.Template Require Import All.

(* Required after MetaRocq so that [string], [ascii] and the [String.*] names
   below are Rocq's and not MetaRocq's bytestrings. *)
From Stdlib Require Import Ascii.
From Stdlib Require Import String.
From Stdlib Require Import Vectors.Vector.

Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

From Stdlib Require Extraction.
Extraction Language Haskell.

Local Open Scope string_scope.

(* Controlling extraction of specific types *)
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]. (* enumeration types *)
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]
.
(* types that require parameters on their constructors *)
(* type, [constructors], recursor *)
Extract Inductive nat => "GHC.Base.Int" ["0" "(\ x -> x Prelude.+ 1)"]
  "(\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))".

(* MetaRocq pulls in Equations' [Signature] machinery. Equations extracts its
   [sigma] to "( * )", which is an OCaml tuple type but not valid Haskell. *)
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive Equations.Init.sigma => "(,)" [ "(,)" ].

Extract Constant plus             => "(Prelude.+)".
Extract Constant mult             => "(Prelude.*)".
Extract Constant PeanoNat.Nat.eqb => "( Prelude.== )".

(* Properly extract the unicode tokens *)
Extract Constant TkStar    => "['★']".
Extract Constant TkArrow   => "['➔']".
Extract Constant TkPi      => "['Π']".
Extract Constant TkAll     => "['∀']".
Extract Constant TkTDot    => "['·']".
Extract Constant TkULam    => "['Λ']".
Extract Constant TkLam     => "['λ']".
Extract Constant TkMu      => "['μ']".
Extract Constant TkDelta   => "['δ']".
Extract Constant TkBeta    => "['β']".
Extract Constant TkEq      => "['≃']".
Extract Constant TkSigma   => "['σ']".

Extract Inductive Ascii.ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr ( (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+ (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+ (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+ (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+ (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+ (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+ (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+ (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".
Extract Inductive Stdlib.Strings.String.string => "Prelude.String" [ "([])" "(:)" ].
Extract Inlined Constant Stdlib.Strings.String.string_dec => "(Prelude.==)".
Extract Inlined Constant Stdlib.Strings.String.eqb => "(Prelude.==)".


(* Adds Everything we will test here *)
MetaRocq Quote Recursively Definition nat_syntax := nat.
MetaRocq Quote Recursively Definition list_syntax := list.
MetaRocq Quote Recursively Definition option_syntax := option.
MetaRocq Quote Recursively Definition vector_syntax := Vectors.Vector.t.
MetaRocq Quote Recursively Definition le_syntax := le.
Definition asgn := nat.
MetaRocq Quote Recursively Definition asgn_syntax := asgn.
MetaRocq Quote Recursively Definition mul_syntax := Nat.mul.

Lemma refl1 : 1 = 1.
Proof.
  exact eq_refl.
Qed.
MetaRocq Quote Recursively Definition refl1_syntax := refl1.

Definition L : Type -> Type :=
fun (A: Type) => forall (X: Type), (A -> X -> X) -> X -> X.

Definition lnil : forall A, L A := fun A X _ n => n.

Definition lcons : forall A, A -> L A -> L A :=
fun A h t X c n => c h (t X c n).

MetaRocq Quote Recursively Definition lnil_syntax := lnil.
MetaRocq Quote Recursively Definition lcons_syntax := lcons.

Lemma nileqnil : List.cons 1 List.nil = List.cons 1 List.nil.
Proof.
  exact eq_refl.
Qed.

MetaRocq Quote Recursively Definition nileqnil_syntax := nileqnil.
MetaRocq Quote Recursively Definition zeroneqS_syntax := O_S.
MetaRocq Quote Recursively Definition iff_syntax := iff.

Set Extraction TypeExpand.
(* We are finally ready to extract the programs we want *)
Extraction "main.hs" PrettySum PrettyProgram denoteCoq
           nat_syntax list_syntax option_syntax vector_syntax le_syntax iff_syntax
           asgn_syntax refl1_syntax lnil_syntax lcons_syntax nileqnil_syntax zeroneqS_syntax mul_syntax.
