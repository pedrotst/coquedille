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

Quote Recursively Definition iff_syntax := iff.
Eval compute in ((denoteCoq iff_syntax)).
Eval compute in (pretty (denoteCoq iff_syntax)).

Quote Recursively Definition and_cancel_l_syntax := and_cancel_l.
Eval compute in ((denoteCoq and_cancel_l_syntax)).
Eval compute in (pretty (denoteCoq and_cancel_l_syntax)).

Inductive Ve (A : Type) : nat -> bool -> nat -> Type :=
| vni : Ve A 0 false 2
| vcon : A -> forall (n : nat), Ve A n false 2 -> Ve A (S n) false 2
.

(* Fixpoint hasNu {A n b m} (v : Ve A n b m) : bool := *)
(* match v with *)
(* | vni => false *)
(* | vcon => inr c *)
(* end. *)

Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : A -> forall (n : nat), Vec A n -> Vec A (S n)
.

(* Test common datatypes *)
Quote Recursively Definition vector_syntax := Vec.
Eval compute in ((denoteCoq vector_syntax)).
Eval compute in (pretty (denoteCoq vector_syntax)).

Quote Recursively Definition nat_syntax := nat.
Eval compute in (pretty (denoteCoq nat_syntax)).
Quote Recursively Definition option_syntax := option.
Eval compute in (pretty (denoteCoq option_syntax)).

Quote Recursively Definition list_syntax :=
ltac:(let t := eval compute in list in exact t).
Eval compute in (pretty (denoteCoq list_syntax)).

Quote Recursively Definition t_syntax :=
ltac:(let t' := eval compute in t in exact t').
Eval compute in (pretty (denoteCoq t_syntax)).

(* Test intricate datatype *)

Inductive mytry : Type :=
| foo
| bar : ((nat -> nat) -> (nat -> list nat)) -> mytry
| asdf : Vec nat 3 -> mytry
.

(* Test Definitions *)
Quote Recursively Definition x1 := (mytry).
Eval compute in (pretty (denoteCoq x1)).

Definition x' := nat.
Definition x := x'.

Quote Recursively Definition x_syntax := x'.
Eval compute in (pretty (denoteCoq x_syntax)).
Eval compute in ((denoteCoq x_syntax)).

Quote Recursively Definition le_syntax := le.
Eval compute in (pretty (denoteCoq le_syntax)).

Definition isZeroFun (n : nat) : nat -> bool :=
match n with
| O => fun _ => true
| S _ => fun _ => false
end.

Quote Recursively Definition isZero_syntax := isZeroFun.
Eval compute in (pretty (denoteCoq isZero_syntax)).

Definition isVnil {A n} (v : t A n) : bool :=
match v with
| nil => true
| cons x n' v' =>  false
end.

Quote Recursively Definition isVnil_syntax := isVnil.
Eval compute in (pretty (denoteCoq isVnil_syntax)).

Fixpoint hasNum {n} (x: nat) (v: t nat n): bool :=
match v with
| nil => false
| cons y size ys => eq_nat x y || hasNum x ys
end.

Quote Recursively Definition hasNum_syntax := hasNum.
Eval compute in ((denoteCoq hasNum_syntax)).
Eval compute in (pretty (denoteCoq hasNum_syntax)).

Fixpoint hasNum' {A n n'} (v: t (t A n') n): bool :=
match v with
| nil => false
| cons y size ys => hasNum' ys
end.

Quote Recursively Definition hasNum'_syntax := hasNum'.
Eval compute in ((denoteCoq hasNum'_syntax)).
Eval compute in (pretty (denoteCoq hasNum'_syntax)).

Fixpoint hasVnil {A n n'} (v: t (t A n') n) : bool :=
match v with
| nil => false
| cons y size ys => if isVnil y then true else hasVnil ys
end.

Arguments cons {_} _ {_}.
Arguments nil {_}.

Program Definition v1 := cons (@nil nat) nil.
Program Definition v2 := cons (@nil nat) v1.

Program Definition v3 := cons (v2) nil.

Eval compute in (isVnil v2).
Eval compute in (hasVnil v3).

Quote Recursively Definition hasVnil_syntax := hasVnil.
Eval compute in ((denoteCoq hasVnil_syntax)).
Eval compute in (pretty (denoteCoq hasVnil_syntax)).

Fixpoint myAdd (n m a b c: nat) {struct m} : nat :=
  match m with
  | 0 => n
  | S p => S (myAdd n p a b c)
  end.

Quote Recursively Definition add_syntax := myAdd.
Eval compute in ((denoteCoq add_syntax)).
Eval compute in (pretty (denoteCoq add_syntax)).

Quote Recursively Definition mul_syntax := Nat.mul.
Eval compute in (pretty (denoteCoq mul_syntax)).

Quote Recursively Definition pow_syntax := Nat.pow.
Eval compute in (pretty (denoteCoq pow_syntax)).

Quote Recursively Definition gcd_syntax := Nat.gcd.
Eval compute in (pretty (denoteCoq gcd_syntax)).

(* Test a straightforward lemma *)
Lemma exlemma : [1] = [1].
Proof.
  exact eq_refl.
Qed.

(* Test Equality *)
Quote Recursively Definition eq_syntax := eq.
Eval compute in ((denoteCoq eq_syntax)).
Eval compute in (pretty (denoteCoq eq_syntax)).

Quote Recursively Definition eqrect_syntax := eq_rect.
Eval compute in ((denoteCoq eqrect_syntax)).
Eval compute in (pretty (denoteCoq eqrect_syntax)).

Quote Recursively Definition exlemma_syntax := exlemma.
Eval compute in (pretty (denoteCoq exlemma_syntax)).
Eval compute in ((denoteCoq exlemma_syntax)).

(* Test JMeq *)
Quote Recursively Definition jmeq_syntax := JMeq.
Eval compute in (pretty (denoteCoq jmeq_syntax)).
Eval compute in ((denoteCoq jmeq_syntax)).

Lemma vector_0_nil {A} :
 forall {n : nat} (v : Vec A n),
   n = 0 -> JMeq v (vnil A).
Proof.
 destruct v; intro.
 - reflexivity.
 - discriminate.
Qed.

Lemma OS' : forall n, 0 <> S n.
Proof.
  discriminate.
Defined.

Quote Recursively Definition False_syntax := False_ind.
Eval compute in (pretty (denoteCoq False_syntax)).

Quote Recursively Definition OS_syntax := O_S.
Eval compute in ((denoteCoq OS_syntax)).
Eval compute in (pretty (denoteCoq OS_syntax)).

Quote Recursively Definition v0nil_syntax := vector_0_nil.
Eval compute in ((denoteCoq v0nil_syntax)).
Eval compute in (pretty (denoteCoq v0nil_syntax)).

Definition t_isnil {A n} (v: t A n) : bool :=
match v with
| nil => true
| cons v' n' t => false
end.

Quote Recursively Definition isnil_syntax := t_isnil.
Eval compute in ((denoteCoq isnil_syntax)).
Eval compute in (pretty (denoteCoq isnil_syntax)).

Definition case0' {A}
          (P : Vec A 0 -> Type)
          (H : P (vnil A))
          (v : Vec A 0)
 : P v.
Proof.
 eapply JMeq_rect.
 - apply H.
 - symmetry.
   eapply vector_0_nil.
   reflexivity.
Defined.

Quote Recursively Definition case0'_syntax := case0'.
Eval compute in ((denoteCoq case0'_syntax)).
Eval compute in (pretty (denoteCoq case0'_syntax)).


Lemma eq_vnil {A} : forall x y : Vec A 0, x = y.
Proof.
    intros.
    pattern y.
    pattern x0.
    repeat apply case0'.
    reflexivity.
Qed.

Quote Recursively Definition eqvnil_syntax := eq_vnil.
Eval compute in ((denoteCoq eqvnil_syntax)).
Eval compute in (pretty (denoteCoq eqvnil_syntax)).

(* vnil <> vcons *)
Lemma Vector_nil_neq_List_nil {A} (a : A) :
  ~ (@vnil A ~= @Datatypes.nil A).
Proof.
  intro H.
  pose proof (@eq_vnil A).
  symmetry in H.
  destruct H.
  pose proof (H0 (@Datatypes.nil A) (Datatypes.cons a Datatypes.nil)).
  discriminate.
Qed.


(* Ced.TApp _ ([(inl eqty); (inr x); _; _; (inr y); (inr eq)]) => *)
Quote Recursively Definition nilvenil_syntax := Vector_nil_neq_List_nil.
Eval compute in (pretty (denoteCoq nilvenil_syntax)).
Eval compute in ((denoteCoq nilvenil_syntax)).

Lemma cons_inj : forall A (z z' y y' : A), [z; z'] = [y; y'] -> z = y /\ z' = y'.
Proof.
  intros.
  inversion H.
  split; reflexivity.
Qed.

Lemma vcons_inj : forall A (z y : A), vcons _ z 0 (vnil A) = vcons A y 0 (vnil A) -> z = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.



Quote Recursively Definition consinj_syntax := vcons_inj.
Eval compute in (pretty (denoteCoq consinj_syntax)).
Eval compute in ((denoteCoq nilvenil_syntax)).

Definition zzzz {A}: forall (z : A), A -> nat := fun (z: A) (_: A) => 1.

Quote Recursively Definition zz_syntax := zzzz.
Eval compute in (pretty (denoteCoq zz_syntax)).

Definition tst_parens := (nil).

Quote Recursively Definition tstparens_syntax := tst_parens.
Eval compute in (pretty (denoteCoq tstparens_syntax)).

Quote Recursively Definition sigT_syntax := sigT.
Eval compute in (pretty (denoteCoq sigT_syntax)).
(*      = "data sigT (A : ★) (P : A ➔ ★) : ★ = *)
(*   | existT : Π x : A . P x ➔ sigT. *)

(* "%string *)
(*      : string *)

Definition let_ex := let x := 1 in S x.
Quote Recursively Definition letex_syntax := let_ex.
Eval compute in (pretty (denoteCoq letex_syntax)).


Quote Recursively Definition IsSucc_syntax := IsSucc.
(* IsSucc =  *)
(* fun n : nat => match n with *)
(*                | 0 => False *)
(*                | S _ => True *)
(*                end *)
(*      : nat -> Prop *)

(* Argument scope is [nat_scope] *)


Eval compute in (pretty (denoteCoq IsSucc_syntax)).
  (* | tCase : inductive * nat -> *)
            (* term -> term -> list (nat * term) -> term *)

(* Quote Recursively Definition falseind_syntax := False_ind. *)
(* False_ind =  *)
(* fun (P : Prop) (f : False) => match f return P with *)
(*                               end *)
(*      : forall P : Prop, False -> P *)

(* Argument scopes are [type_scope _] *)


(* Eval compute in (pretty (denoteCoq falseind_syntax)). *)

Definition L : Type -> Type :=
fun (A: Type) => forall (X: Type), (A -> X -> X) -> X -> X.

Definition Lnil : forall A: Type, L A :=
fun (A X : Type) (_ : A -> X -> X) (n : X) => n.

Definition Lcons : forall A, A -> L A -> L A :=
fun A h t X c n => c h (t X c n).

Quote Recursively Definition idprop_syntax := VectorDef.case0.
Eval compute in (pretty (denoteCoq idprop_syntax)).

Quote Recursively Definition L_syntax := L.
Eval compute in (pretty (denoteCoq L_syntax)).
Eval compute in ((denoteCoq L_syntax)).

Quote Recursively Definition Lnil_syntax := Lnil.
Eval compute in (pretty (denoteCoq Lnil_syntax)).

Quote Recursively Definition Lcons_syntax := Lcons.
Eval compute in (pretty (denoteCoq Lcons_syntax)).

(* Quote Recursively Definition nilvenil_syntax := Vector_nil_neq_List_nil. *)
(* Eval compute in (pretty (denoteCoq plus_syntax)). *)

Eval compute in (let r := (denoteCoq exlemma_syntax) in
                 match r with
                 | inr p => showState p
                 | _ => []
                 end).

