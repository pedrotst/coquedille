Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

Require Import String.
Require Import List. Import ListNotations.

Quote Recursively Definition nat_syntax := nat.
Quote Recursively Definition option_syntax := option.

Require Import Vectors.Vector.
Local Open Scope string_scope.

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


Definition program_err (p : option CedProgram): CedProgram :=
  match p with
  | None => []
  | Some v => v
  end.

Definition denotenat := program_err (denoteCoq nat_syntax).
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


Definition denoteoption := program_err (denoteCoq option_syntax).
Print option_syntax.

(* ind_ctors := [("Some", *)
(*                tProd (nNamed "A") *)
(*                      (tSort *)
(*                         (Universe.make'' *)
(*                            (Level.Level *)
(*                               "Coq.Init.Datatypes.13", *)
(*                             false) [])) *)
(*                      (tProd nAnon  *)
(*                             (tRel 0) *)
(*                             (tApp (tRel 2) [tRel 1])), 1); *)
(*               ("None", *)
(*                tProd (nNamed "A") *)
(*                      (tSort *)
(*                         (Universe.make'' *)
(*                            (Level.Level *)
(*                               "Coq.Init.Datatypes.13", *)
(*                             false) [])) *)
(*                      (tApp (tRel 1) [tRel 0]), 0)]; *)
Eval compute in denoteoption.
     (* = [CmdData *)
     (*      (DefData "option" KdStar *)
     (*         [Ctr "Some" *)
     (*            (TpPi (cName "A") (TpVar "NotImpl") *)
     (*               (TpPi cAnon (TpVar "NotImpl") (TpVar "NotImpl"))); *)
     (*         Ctr "None" *)
     (*           (TpPi (cName "A") (TpVar "NotImpl") *)
     (*              (TpVar "NotImpl"))])] *)
     (* : CedProgram *)

Eval compute in (ppProgram denoteoption).
Eval compute in (ppProgram denotenat).
Local Close Scope string_scope.
