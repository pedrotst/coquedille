Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

Require Import String.
Require Import List. Import ListNotations.
Require Import Vectors.Vector.

Quote Recursively Definition nat_syntax := nat.
Quote Recursively Definition option_syntax := option.

Quote Recursively Definition list_syntax :=
ltac:(let t := eval compute in list in exact t).

Quote Recursively Definition vector_syntax := t.


Inductive mytry : Type :=
| foo
| bar : (nat -> nat) -> nat -> mytry
.

Quote Recursively Definition x1 := (mytry).
Eval compute in (pretty (denoteCoq x1)).

Eval compute in (pretty (denoteCoq vector_syntax)).
Eval compute in (pretty (denoteCoq vector_syntax)).
Eval compute in (pretty (denoteCoq list_syntax)).

Definition x' := nat.
Definition x := x'.

Inductive myDep (A : Type) : x -> Type :=
| mynil : myDep A 0
| mycons : A -> forall x, myDep A x -> myDep A (S x)
.

Quote Recursively Definition myDep_syntax := 2.

Eval compute in (pretty (denoteCoq vector_syntax)).

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


(* Definition program_err (p : option Ced.Program): Ced.Program := *)
  (* match p with *)
  (* | None => [] *)
  (* | Some v => v *)
  (* end. *)

Definition denotenat := (denoteCoq nat_syntax).
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
(*   | O : nat *)
(*   | S : Π anon : nat . nat. *)
(* " *)
(*      : string *)


Definition denoteoption := (denoteCoq option_syntax).
Print option_syntax.

(* ind_params := [{| decl_name := nNamed "A"; *)
(*                   decl_body := None; *)
(*                   decl_type := tSort *)
(*                                  (Universe.make'' *)
(*                                    (Level.Level *)
(*                                      "Coq.Init.Datatypes.13", *)
(*                                      false) []) |}]; *)

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
(* = [Ced.CmdData *)
(*      (Ced.DefData "option" Ced.KdStar *)
(*         [Ced.Ctr "Some" *)
(*            (Ced.TpPi (Ced.Named "A") Ced.KdStar *)
(*               (Ced.TpPi Ced.Anon Ced.KdStar *)
(*                  (Ced.TpVar "notimpl"))); *)
(*         Ced.Ctr "None" *)
(*           (Ced.TpPi (Ced.Named "A") Ced.KdStar *)
(*              (Ced.TpVar "notimpl"))])] *)
(* : Ced.Program *)

Eval compute in (pretty denoteoption).
(*      = "data option (A : ★) : ★ := *)
(*   | Some : A ➔ option ·A *)
(*   | None : option ·A. *)
(* " *)
(*      : string *)

Eval compute in (pretty denotenat).
(*      = "data nat : ★ := *)
(*   | O : nat *)
(*   | S : nat ➔ nat. *)
(* " *)
(*      : string *)

Definition denotelist := (denoteCoq list_syntax).
Print list_syntax.
Eval compute in (pretty denotelist).
(*      = "data list (A : ★) : ★ := *)
(*   | nil : list ·A *)
(*   | cons : A ➔ list ·A ➔ list ·A. *)
(* " *)
(*      : string *)

Inductive mydata (A B C: Type) (D : nat -> Type) :=
| foo' : A -> mydata A B C D
| bar' : B -> C -> mydata A B C D
| baz' : forall x, D x -> mydata A B C D
.

Quote Recursively Definition mydata_syntax := mydata.
Print mydata_syntax.
(* mydata_syntax =  *)
(* ([InductiveDecl "Coq.Init.Datatypes.nat" *)
(* ind_ctors := [("foo'", *)
(*               tProd (nNamed "A") *)
(*                 (tSort *)
(*                    (Universe.make'' *)
(*                       (Level.Level "Top.23", *)
(*                       false) [])) *)
(*                 (tProd (nNamed "B") *)
(*                    (tSort *)
(*                       (Universe.make'' *)
(*                          ( *)
(*                          Level.Level "Top.24", *)
(*                          false) [])) *)
(*                    (tProd  *)
(*                       (nNamed "C") *)
(*                       (tSort *)
(*                          (Universe.make'' *)
(*                          ( *)
(*                          Level.Level "Top.25", *)
(*                          false) [])) *)
(*                       (tProd  *)
(*                          (nNamed "D") *)
(*                          (tProd nAnon *)
(*                          (tInd *)
(*                          {| *)
(*                          inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                          inductive_ind := 0 |} []) *)
(*                          (tSort *)
(*                          (Universe.make'' *)
(*                          ( *)
(*                          Level.Level "Top.26", *)
(*                          false) []))) *)
(*                          (tProd nAnon  *)
(*                          (tRel 3) *)
(*                          (tApp  *)
(*                          (tRel 5) *)
(*                          [ *)
(*                          tRel 4;  *)
(*                          tRel 3;  *)
(*                          tRel 2;  *)
(*                          tRel 1]))))), 1); *)
(* Inductive mydata (A B C: Type) (D : nat -> Type) := *)
(* | foo' : A -> mydata A B C D *)


Definition denotemydata := (denoteCoq mydata_syntax).


Eval compute in (pretty denotemydata).
(* [ _, _, _, B, _, A] *)
(*      = "data mydata (A : ★) (B : ★) (C : ★) (D : notimpl ➔ ★) : ★ := *)
(*   | foo' : B ➔ A ·B ·C ·dummy ·D *)
(*   | bar' : C ➔ dummy ➔ A ·B ·C ·dummy ·D *)
(*   | baz' : Π x : notimpl . D ·x ➔ A ·B ·C ·dummy ·D. *)
(* " *)
(*      : string *)
Inductive tst :=
  | tstctor1 : forall A B C, A -> B -> C -> tst.

Quote Recursively Definition tst_syntax := tst.
Print tst_syntax.
Definition denotetst := (denoteCoq tst_syntax).
Eval compute in denotetst.
Eval compute in (pretty denotetst).
