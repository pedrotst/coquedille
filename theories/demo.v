Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

Require Import Coq.Program.Equality.
Require Import String.
Require Import List. Import ListNotations.
Require Import Coq.Vectors.Vector.


Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : A -> forall (n : nat), Vec A n -> Vec A (S n)
.

Quote Recursively Definition vector_syntax := Vec.
(* vector_syntax =  *)
(* ([InductiveDecl "Coq.Init.Datatypes.nat"%string *)
(*     {| *)
(*     ind_finite := Finite; *)
(*     ind_npars := 0; *)
(*     ind_params := []; *)
(*     ind_bodies := [{| *)
(*                    ind_name := "nat"%string; *)
(*                    ind_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.lSet, false) []); *)
(*                    ind_kelim := [InProp; InSet; InType]; *)
(*                    ind_ctors := [("O"%string, tRel 0, 0); *)
(*                                 ("S"%string, *)
(*                                 tProd nAnon (tRel 0) (tRel 1), 1)]; *)
(*                    ind_projs := [] |}]; *)
(*     ind_universes := Monomorphic_ctx *)
(*                        (LevelSetProp.of_list [], *)
(*                        ConstraintSet.empty) |}; *)
(*  InductiveDecl "Top.Vec"%string *)
(*    {| *)
(*    ind_finite := Finite; *)
(*    ind_npars := 1; *)
(*    ind_params := [{| *)
(*                   decl_name := nNamed "A"%string; *)
(*                   decl_body := None; *)
(*                   decl_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.Level "Top.1", false) []) |}]; *)
(*    ind_bodies := [{| *)
(*                   ind_name := "Vec"%string; *)
(*                   ind_type := tProd (nNamed "A"%string) *)
(*                                 (tSort *)
(*                                    (Universe.make'' *)
(*                                       (Level.Level "Top.1", false) *)
(*                                       [])) *)
(*                                 (tProd nAnon *)
(*                                    (tInd *)
(*                                       {| *)
(*                                       inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                       inductive_ind := 0 |} []) *)
(*                                    (tSort *)
(*                                       (Universe.make'' *)
(*                                          (Level.lSet, false) *)
(*                                          [(Level.Level "Top.1", *)
(*                                           false)]))); *)
(*                   ind_kelim := [InProp; InSet; InType]; *)
(*                   ind_ctors := [("vnil"%string, *)
(*                                 tProd (nNamed "A"%string) *)
(*                                   (tSort *)
(*                                      (Universe.make'' *)
(*                                         (Level.Level "Top.1", *)
(*                                         false) [])) *)
(*                                   (tApp (tRel 1) *)
(*                                      [tRel 0; *)
(*                                      tConstruct *)
(*                                        {| *)
(*                                        inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                        inductive_ind := 0 |} 0 []]), *)
(*                                 0); *)
(*                                ("vcons"%string, *)
(*                                tProd (nNamed "A"%string) *)
(*                                  (tSort *)
(*                                     (Universe.make'' *)
(*                                        (Level.Level "Top.1", false) *)
(*                                        [])) *)
(*                                  (tProd nAnon  *)
(*                                     (tRel 0) *)
(*                                     (tProd (nNamed "n"%string) *)
(*                                        (tInd *)
(*                                           {| *)
(*                                           inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                           inductive_ind := 0 |} []) *)
(*                                        (tProd nAnon *)
(*                                           (tApp  *)
(*                                            (tRel 3) *)
(*                                            [tRel 2; tRel 0]) *)
(*                                           (tApp  *)
(*                                            (tRel 4) *)
(*                                            [ *)
(*                                            tRel 3; *)
(*                                            tApp *)
(*                                            (tConstruct *)
(*                                            {| *)
(*                                            inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                            inductive_ind := 0 |} 1 *)
(*                                            []) [ *)
(*                                            tRel 1]])))), 3)]; *)
(*                   ind_projs := [] |}]; *)
(*    ind_universes := Monomorphic_ctx *)
(*                       (LevelSetProp.of_list [Level.Level "Top.1"], *)
(*                       ConstraintSet.empty) |}], *)
(* tInd {| inductive_mind := "Top.Vec"; inductive_ind := 0 |} []) *)
(*      : program *)

Eval compute in ((denoteCoq vector_syntax)).
Eval compute in (pretty (denoteCoq vector_syntax)).

Quote Recursively Definition nat_syntax := nat.
Eval compute in (pretty (denoteCoq nat_syntax)).
Quote Recursively Definition option_syntax := option.
Eval compute in (pretty (denoteCoq option_syntax)).

Quote Recursively Definition list_syntax :=
ltac:(let t := eval compute in list in exact t).
Eval compute in (pretty (denoteCoq list_syntax)).

(* Quote Recursively Definition vector_syntax := Vector.t. *)


Inductive mytry : Type :=
| foo
| bar : ((nat -> nat) -> (nat -> list nat)) -> mytry
| asdf : Vec nat 3 -> mytry
.

Quote Recursively Definition x1 := (mytry).
Eval compute in (pretty (denoteCoq x1)).

Eval compute in (pretty (denoteCoq nat_syntax)).
Eval compute in (pretty (denoteCoq list_syntax)).
Eval compute in (pretty (denoteCoq option_syntax)).
Eval compute in (pretty (denoteCoq vector_syntax)).

Definition x' := nat.
Definition x := x'.

Quote Recursively Definition x_syntax := x'.
Eval compute in (pretty (denoteCoq x_syntax)).
Eval compute in ((denoteCoq x_syntax)).

Quote Recursively Definition le_syntax := le.
Eval compute in (pretty (denoteCoq le_syntax)).

Inductive myDep (A : Type) : x -> Type :=
| mynil : myDep A 0
| mycons : A -> forall x, myDep A x -> myDep A (S x)
.

Quote Recursively Definition myDep_syntax := myDep.
Eval compute in (pretty (denoteCoq myDep_syntax)).

Lemma exlemma : 1 = 1.
Proof.
  exact eq_refl.
Qed.

Quote Recursively Definition eq_syntax := eq.
(* Inductive eq (A : Type) (x : A) : A -> Prop := *)
(* eq_refl : x = x *)
Eval compute in ((denoteCoq eq_syntax)).
Eval compute in (pretty (denoteCoq eq_syntax)).

Quote Recursively Definition exlemma_syntax := exlemma.
Eval compute in (pretty (denoteCoq exlemma_syntax)).

Quote Recursively Definition jmeq_syntax := JMeq.
Eval compute in (pretty (denoteCoq jmeq_syntax)).

Lemma Vector_nil_neq_List_nil {A} (a : A):
  ~ (@nil A ~= @Datatypes.nil A).
Proof.
  intro H.
  inversion H.
  clear H0.
  assert (forall x y : Vector.t A 0, x = y). {
    clear.
    intros.
    pattern y.
    pattern x0.
    repeat apply VectorDef.case0.
    reflexivity.
  }
  rewrite H1 in H0.
  pose proof (H0 (@Datatypes.nil A) (Datatypes.cons a Datatypes.nil)).
  discriminate.
Qed.

Definition zzzz := (fun x: nat -> nat => x) (fun x: nat => x).

Quote Recursively Definition False_syntax := False.
Eval compute in (pretty (denoteCoq False_syntax)).
Quote Recursively Definition True_syntax := True.
Eval compute in (pretty (denoteCoq True_syntax)).

Definition tst_parens := (nil).

Quote Recursively Definition tstparens_syntax := tst_parens.
Eval compute in (pretty (denoteCoq tstparens_syntax)).

Quote Recursively Definition sigT_syntax := sigT.
Eval compute in (pretty (denoteCoq sigT_syntax)).
(*      = "data sigT (A : ★) (P : A ➔ ★) : ★ = *)
(*   | existT : Π x : A . P x ➔ sigT. *)

(* "%string *)
(*      : string *)

Quote Recursively Definition falseind_syntax := False_ind.
Eval compute in (pretty (denoteCoq falseind_syntax)).

Definition L : Type -> Type :=
fun (A: Type) => forall (X: Type), (A -> X -> X) -> X -> X.

Definition Lnil : forall A, L A := fun A X _ n => n.

Definition Lcons : forall A, A -> L A -> L A :=
fun A h t X c n => c h (t X c n).

Quote Recursively Definition idprop_syntax := VectorDef.case0.
Eval compute in (pretty (denoteCoq idprop_syntax)).

Quote Recursively Definition L_syntax := L.
Eval compute in (pretty (denoteCoq L_syntax)).

Quote Recursively Definition nilvenil_syntax := Vector_nil_neq_List_nil.
Eval compute in (pretty (denoteCoq nilvenil_syntax)).
Quote Recursively Definition nilvenil_syntax := Vector_nil_neq_List_nil.
Eval compute in (pretty (denoteCoq plus_syntax)).

Eval compute in (let r := (denoteCoq exlemma_syntax) in
                 match r with
                 | inr p => showState p
                 | _ => []
                 end).

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

(* Inductive foo : Type := *)
(* | bar : foo *)
(* | baz : bool -> foo -> foo *)
(* | buz : forall x: nat, Vector.t bool x -> foo -> bool -> foo *)
(* . *)


(* Quote Recursively Definition myNat_syntax := myNat. *)
(* Quote Recursively Definition foo_syntax := foo. *)
(* Print myNat_syntax. *)
(* Print foo_syntax. *)


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

Inductive tst_data (A B C : Type) :=
| tst_ctor : C -> A -> B -> tst_data B C B -> tst_data A B C
.

Quote Recursively Definition tstdata_syntax := tst_data.
Definition xxx := denoteCoq tstdata_syntax.
Eval compute in xxx.
(* tstdata_syntax =  *)
(* ([InductiveDecl "Top.tst_data" *)
(*     {| *)
(*     ind_finite := Finite; *)
(*     ind_npars := 3; *)
(*     ind_params := [{| *)
(*                    decl_name := nNamed "C"; *)
(*                    decl_body := None; *)
(*                    decl_type := tSort *)
(*                                   (Universe.make'' *)
(*                                      (Level.Level "Top.136", false) *)
(*                                      []) |}; *)
(*                   {| *)
(*                   decl_name := nNamed "B"; *)
(*                   decl_body := None; *)
(*                   decl_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.Level "Top.135", false) *)
(*                                     []) |}; *)
(*                   {| *)
(*                   decl_name := nNamed "A"; *)
(*                   decl_body := None; *)
(*                   decl_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.Level "Top.134", false) *)
(*                                     []) |}]; *)
(*     ind_bodies := [{| *)
(*                    ind_name := "tst_data"; *)
(*                    ind_type := tProd (nNamed "A") *)
(*                                  (tSort *)
(*                                     (Universe.make'' *)
(*                                        (Level.Level "Top.134", *)
(*                                        false) [])) *)
(*                                  (tProd (nNamed "B") *)
(*                                     (tSort *)
(*                                        (Universe.make'' *)
(*                                           (Level.Level "Top.135", *)
(*                                           false) [])) *)
(*                                     (tProd (nNamed "C") *)
(*                                        (tSort *)
(*                                           (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.136", *)
(*                                            false) [])) *)
(*                                        (tSort *)
(*                                           (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.134", *)
(*                                            false) *)
(*                                            [ *)
(*                                            ( *)
(*                                            Level.Level "Top.135", *)
(*                                            false); *)
(*                                            ( *)
(*                                            Level.Level "Top.136", *)
(*                                            false)])))); *)
(*                    ind_kelim := [InProp; InSet; InType]; *)
(*                    ind_ctors := [("tst_ctor", *)
(*                                  tProd (nNamed "A") *)
(*                                    (tSort *)
(*                                       (Universe.make'' *)
(*                                          (Level.Level "Top.134", *)
(*                                          false) [])) *)
(*                                    (tProd (nNamed "B") *)
(*                                       (tSort *)
(*                                          (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.135", *)
(*                                            false) [])) *)
(*                                       (tProd  *)
(*                                          (nNamed "C") *)
(*                                          (tSort *)
(*                                            (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.136", *)
(*                                            false) [])) *)
(*                                          (tProd nAnon  *)
(*                                            (tRel 0) *)
(*                                            (tProd nAnon  *)
(*                                            (tRel 3) *)
(*                                            (tProd nAnon  *)
(*                                            (tRel 3) *)
(*                                            (tApp  *)
(*                                            (tRel 6) *)
(*                                            [tRel 5; tRel 4; tRel 3])))))), *)
(*                                  3)]; *)
(*                    ind_projs := [] |}]; *)
(*     ind_universes := Monomorphic_ctx *)
(*                        (LevelSetProp.of_list *)
(*                           [Level.Level "Top.136"; *)
(*                           Level.Level "Top.135"; *)
(*                           Level.Level "Top.134"], *)
(*                        ConstraintSet.empty) |}], *)
(* tInd {| inductive_mind := "Top.tst_data"; inductive_ind := 0 |} []) *)
(*      : program *)



Eval compute in (pretty (denoteCoq tstdata_syntax)).

Inductive tst_data2 (A : Type) (D : nat -> Type ) :=
| tst_ctor2 : A -> tst_data2 A D
.

Quote Recursively Definition tstdata2_syntax := tst_data2.
Definition xx := denoteCoq tstdata2_syntax.
Eval compute in xx.
(* tstdata2_syntax =  *)
(* ([InductiveDecl "Top.tst_data2" *)
(*     {| *)
(*     ind_finite := Finite; *)
(*     ind_npars := 2; *)
(*     ind_params := [{| *)
(*                    decl_name := nNamed "D"; *)
(*                    decl_body := None; *)
(*                    decl_type := tProd nAnon *)
(*                                   (tSort *)
(*                                      (Universe.make'' *)
(*                                         (Level.lProp, false) [])) *)
(*                                   (tSort *)
(*                                      (Universe.make'' *)
(*                                         (Level.Level "Top.163", *)
(*                                         false) [])) |}; *)
(*                   {| *)
(*                   decl_name := nNamed "A"; *)
(*                   decl_body := None; *)
(*                   decl_type := tSort *)
(*                                  (Universe.make'' *)
(*                                     (Level.Level "Top.162", false) *)
(*                                     []) |}]; *)
(*     ind_bodies := [{| *)
(*                    ind_name := "tst_data2"; *)
(*                    ind_type := tProd (nNamed "A") *)
(*                                  (tSort *)
(*                                     (Universe.make'' *)
(*                                        (Level.Level "Top.162", *)
(*                                        false) [])) *)
(*                                  (tProd (nNamed "D") *)
(*                                     (tProd nAnon *)
(*                                        (tSort *)
(*                                           (Universe.make'' *)
(*                                            (Level.lProp, false) [])) *)
(*                                        (tSort *)
(*                                           (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.163", *)
(*                                            false) []))) *)
(*                                     (tSort *)
(*                                        (Universe.make'' *)
(*                                           (Level.Level "Top.162", *)
(*                                           false) []))); *)
(*                    ind_kelim := [InProp; InSet; InType]; *)
(*                    ind_ctors := [("tst_ctor2", *)
(*                                  tProd (nNamed "A") *)
(*                                    (tSort *)
(*                                       (Universe.make'' *)
(*                                          (Level.Level "Top.162", *)
(*                                          false) [])) *)
(*                                    (tProd (nNamed "D") *)
(*                                       (tProd nAnon *)
(*                                          (tSort *)
(*                                            (Universe.make'' *)
(*                                            (Level.lProp, false) [])) *)
(*                                          (tSort *)
(*                                            (Universe.make'' *)
(*                                            ( *)
(*                                            Level.Level "Top.163", *)
(*                                            false) []))) *)
(*                                       (tProd nAnon  *)
(*                                          (tRel 1) *)
(*                                          (tApp  *)
(*                                            (tRel 3) *)
(*                                            [tRel 2; tRel 1]))), 1)]; *)
(*                    ind_projs := [] |}]; *)
(*     ind_universes := Monomorphic_ctx *)
(*                        (LevelSetProp.of_list *)
(*                           [Level.Level "Top.163"; *)
(*                           Level.Level "Top.162"], *)
(*                        ConstraintSet.empty) |}], *)
(* tInd {| inductive_mind := "Top.tst_data2"; inductive_ind := 0 |} []) *)
(*      : program *)

Eval compute in (pretty (denoteCoq tstdata2_syntax)).
(*      = "data nat : ★ = *)
(*   | O : nat *)
(*   | S : nat ➔ nat. *)

(* data tst_data2 (A : ★) (D : nat ➔ ★) : ★ = *)
(*   | tst_ctor2 : dummy ➔ A ·dummy ·D. *)

(* _ = tst_data2. *)

(* " *)
(*      : string *)
