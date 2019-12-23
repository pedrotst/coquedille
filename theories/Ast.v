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
  | TyLam (_: Name) (_: Typ) (_: Typ)
  | TyAllT (_: Name) (_: Typ) (_: Typ)
  | TyIntersec (_: Name) (_: Typ) (_: Typ)
  | TyEq (_: Typ) (_: Typ)
  .

  Inductive Term : Type :=
  | TVar (_: Var)
  | TLam (_: Name) (_: Term) (_: Term)
  | TApp (_: Term) (_: list (Term + Typ))
  | TLamK (_: Name) (_: Kind) (_: Term)
  | TLamT (_: Name) (_: Typ) (_: Term)
  .

  (* Definition TermTy : Type := Term + Typ. *)
  (* Definition ListTermTy : Type := list TermTy. *)
  Coercion injT x : (Term + Typ) := inl x.
  Coercion injTy x : (Term + Typ) := inr x.

  Definition inj1List {A B} l : list (A + B) := map inl l.
  Definition inj2List {A B} l : list (A + B) := map inr l.

  (* Identity Coercion id : ListTermTy >-> list. *)

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Term).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * Term).

  Inductive Data : Type :=
  | DefData (_: Var) (_: Params) (_: Term) (_: Ctors).

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
