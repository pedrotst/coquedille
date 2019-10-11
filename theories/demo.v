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


Definition program_err (p : option Ced.Program): Ced.Program :=
  match p with
  | None => []
  | Some v => v
  end.

Definition denotenat := program_err (denoteCoq nat_syntax).
Print nat_syntax.
(* nat_syntax =  *)
(* ([InductiveDecl "Coq.Init.Datatypes.nat" *)
(*     {| *)
(*     ind_finite := Finite; *)
(*     ind_npars := 0; *)
(*     ind_params := []; *)
(*     ind_bodies := [{| *)
(*                    ind_name := "nat"; *)
(*                    ind_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.lSet, false) []); *)
(*                    ind_kelim := [InProp; InSet; InType]; *)
(*                    ind_ctors := [("O", tRel 0, 0); *)
(*                                 ("S", *)
(*                                 tProd nAnon (tRel 0) (tRel 1), 1)]; *)
(*                    ind_projs := [] |}]; *)
(*     ind_universes := Monomorphic_ctx *)
(*                        (LevelSetProp.of_list [], *)
(*                        ConstraintSet.empty) |}], *)
(* tInd *)
(*   {| *)
(*   inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*   inductive_ind := 0 |} []) *)
(*      : program *)

Eval compute in denotenat.
(* = [CmdData *)
(*      (DefData "nat" KdStar *)
(*         [Ctr "O" (TpVar "nat"); *)
(*         Ctr "S" (TpPi cAnon (TpVar "nat") (TpVar "nat"))])] *)
(* : CedProgram *)
Eval compute in (pretty denotenat).
(*      = "  data nat : ★ :=  *)
(*           | O : nat *)
(*           | S : ∀ anon :nat . nat. *)
(* " *)
(*      : string *)


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

Eval compute in (pretty denoteoption).
(*      = "  data option : ★ :=  *)
(*   | Some : Π A : notimpl . Π anon : notimpl . notimpl *)
(*   | None : Π A : notimpl . notimpl. *)
(* " *)
(*      : string *)


Eval compute in (pretty denotenat).
Local Close Scope string_scope.
