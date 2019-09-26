Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
(* Require Import String. *)

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

Definition ced_context := list CedType.

(* Notation "Γ ,, x" := (x :: Γ) (at level 20). *)

Reserved Notation "⟦ x ⟧" (at level 0).

Definition nname_cname (n: name): Name :=
  match n with
  | nAnon => cAnon
  | nNamed c => cName c
  end.

Open Scope string_scope.

Fixpoint denoteTerm (t: term) {struct t}: State ced_context CedType :=
  let default := TpVar "x" in
  match t with
  | tProd x t1 t2 =>
    t1' <- ⟦ t1 ⟧ ;
    Γ <- get ;
    put (Γ ,, t1') ;;
    t2'  <- ⟦ t2 ⟧ ;
    let cname := nname_cname x in
    pure (TpPi cname t1' t2')
  | tRel n =>
    Γ <- get ;
    match nth_error Γ n with
    | None => return_ default
    | Some x => return_ x
    end
  | _ => pure default
  end
where "⟦ x ⟧" := (denoteTerm x).

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
