Require Import MetaCoq.Template.All.

(* Module C := MetaCoq.Template.All. *)

Require Import Coquedille.Ast.


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

Definition default_t x := [CmdDef (DefTerm x (VarT x))].

Import MonadNotation.
Definition ced_context := list CedType.

(* Notation "Γ ,, x" := (x :: Γ) (at level 20). *)

Reserved Notation "⟦ Γ ̇ x ⟧" (at level 0).

Definition nname_cname (n: name): Name :=
  match n with
  | nAnon => cAnon
  | nNamed c => cName c
  end.

Fixpoint denoteTerm (t: term) (Γ: ced_context) {struct t}: CedType :=
  let default := TpVar "x" in
  match t with
  | tProd x t1 t2 =>
    let t1' := ⟦ Γ ̇ t1 ⟧ in
    let t2' := ⟦ (Γ ,, t1') ̇ t2 ⟧ in
    let cname := nname_cname x in
    (TpPi cname t1' t2')
  | tRel n =>
    match nth_error Γ n with
    | None => default
    | Some x => x
    end
  | _ => default
  end
where "⟦ Γ ̇ x ⟧" := (denoteTerm x Γ).

Fixpoint denoteCtors (ctor: (ident × term) × nat): CedCtor  :=
  let '(name, t, i) := ctor in
  denoteTerm t

Fixpoint denoteCoq (p: program): option CedCmds :=
  let (genv, t) := p in
  match t with
  | tInd ind univ =>
    let mind := inductive_mind ind in
    body <- lookup_mind_decl mind genv ;;
    i_body <- head (ind_bodies body) ;;
    let name := (ind_name i_body) in
    let ctors := ind_ctors i_body in
    ret [CmdData (DefData name KdStar (fmap denoteCtors ctors))]
  | _ => None
  end.

Definition denotenat := denoteCoq nat_syntax.
Definition denoteoption := denoteCoq option_syntax.
Print nat_syntax.

Eval compute in denotenat.
Eval compute in denoteoption.
