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
  | KdAll (_: Name) (_: Kind + Typ) (_: Kind)
  with Typ : Type :=
  | TyVar (_: Var)
  | TyAll (_: Name) (_: Kind) (_: Typ)
  | TyPi (_: Name) (_: Typ) (_: Typ)
  | TyApp (_: Typ) (_: list (Typ + Term))
  | TyLam (_: Name) (_: Typ) (_: Typ)
  | TyLamK (_: Name) (_: Kind) (_: Typ)
  | TyAllT (_: Name) (_: Typ) (_: Typ)
  | TyIntersec (_: Name) (_: Typ) (_: Typ)
  | TyEq (_: Typ) (_: Typ)
  with Term : Type :=
  | TVar (_: Var)
  | TLam (_: Name) (erased: bool) (_: Typ) (_: Term)
  | TLamK (_: Name) (_: Kind) (_: Term)
  | TApp (_: Term) (_: list (Typ + Term))
  .

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Typ).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * (Kind+Typ)).

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
