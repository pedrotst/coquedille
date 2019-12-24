Require Import String.
Require Import List. Import ListNotations.

(* We put all the AST inside a module to avoid name clashes *)
(* with MetaCoq *)
(* In order to use this module without the Ced prefix do: *)
(* Require Import Coquedille.Ast. *)
(* Import Ced. *)
Module Ced.
  Definition Var := string.

  Inductive Name : Type :=
  | Anon
  | Named (_: Var)
  .

  Inductive Kind : Type :=
  | KdStar
      (* Should be Kind+Typ *)
  | KdAll (_: Name) (_: Kind) (_: Kind).

  Inductive Typ : Type :=
  | TyVar (_: Var)
  | TyAll (_: Name) (_: Kind) (_: Typ)
  | TyPi (_: Name) (_: Typ) (_: Typ)
  (* Should be list  of Typ+Term *)
  | TyApp (_: Typ) (_: list Typ)
  | TyLam (_: Name) (_: Typ) (_: Typ)
  | TyAllT (_: Name) (_: Typ) (_: Typ)
  | TyIntersec (_: Name) (_: Typ) (_: Typ)
  | TyEq (_: Typ) (_: Typ)
  .

  Inductive Term : Type :=
  | TVar (_: Var)
  | TLam (_: Name) (_: Term) (_: Term)
  | TApp (_: Term) (_: list (Typ + Term))
  | TLamK (_: Name) (_: Kind) (_: Term)
  | TLamT (_: Name) (_: Typ) (_: Term)
  .

  (* Definition TermTy : Type := Term + Typ. *)
  (* Definition ListTermTy : Type := list TermTy. *)
  Definition TTy : Type := Typ + Term.
  Coercion injTTy x : TTy := inr x.
  Coercion injTyT x : TTy := inl x.

  Definition KTy : Type := Kind + Typ.
  Coercion injKTy x : KTy := inl x.
  Coercion injTyK x : KTy := inr x.

  Definition inj1List {A B} l : list (A + B) := map inl l.
  Definition inj2List {A B} l : list (A + B) := map inr l.

  (* Identity Coercion id : ListTermTy >-> list. *)

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Typ).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * KTy).

  Inductive Data : Type :=
  | DefData (_: Var) (_: Params) (_: Kind) (_: Ctors).

  Inductive Assgn : Type :=
  | AssgnTerm (_: Var) (_: option Typ) (_: Term)
  | AssgnType (_: Var) (_: option Kind) (_: Typ)
  .

  Inductive Cmd : Type :=
  | CmdAssgn (_: Assgn)
  | CmdData (_: Data)
  .
Definition Program := list Cmd.
End Ced.
