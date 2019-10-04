Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Coquedille.DenoteCoq.

Require Import List. Import ListNotations.

Quote Recursively Definition nat_syntax := nat.
Quote Recursively Definition option_syntax := option.

Require Import Vectors.Vector.

Inductive myBool : Type :=
| t
| f
.

Inductive myNat : Type :=
| z : myNat
| s : myBool -> myNat
| bs : myBool-> myBool-> myNat
| ssv : myNat -> myBool-> myNat
| bsv : myNat -> myNat -> myNat
(* | ss : bool -> myNat -> myNat -> myNat *)
(* | sv : forall x, Vector.t nat x -> myNat *)
.

Inductive foo : Type :=
| bar : foo
| baz : bool -> foo -> foo
| buz : forall x: nat, Vector.t bool x -> foo -> bool -> foo
.

Quote Recursively Definition myNat_syntax := myNat.
Quote Recursively Definition foo_syntax := foo.
Print myNat_syntax.
Print foo_syntax.


Definition denotenat := denoteCoq nat_syntax.
Definition denoteoption := denoteCoq option_syntax.
Print nat_syntax.

Eval compute in denotenat.
(*
     = Just
         [CmdData
            (DefData "nat" KdStar
               [Ctr "O" (TpVar "x");
               Ctr "S" (TpPi cAnon (TpVar "x") (TpVar "x"))])]
     : Maybe CedCmds
 *)

Eval compute in denoteoption.
