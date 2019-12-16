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

  Inductive Term : Type :=
  | TPi (_: Name) (_: Term) (_: Term)
  | TApp (_: Term) (_: list Term)
  | TVar (_: Var)
  | TLam (_: Name) (_: Term) (_: Term)
  | KdStar
  .

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Term).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * Term).

  Inductive Data : Type :=
  | DefData (_: Var) (_: Params) (_: Term) (_: Ctors).

  Inductive Assgn : Type :=
  | AssgnType (_: Var) (_: option Term) (_: Term)
  .

  Inductive Cmd : Type :=
  | CmdAssgn (_: Assgn)
  | CmdData (_: Data)
  .
Definition Program := list Cmd.
End Ced.
