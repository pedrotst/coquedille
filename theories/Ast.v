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

  Inductive PrTerm : Type :=
  | PrVar (_: nat)
  | PrRef (_: Var)
  | PrLam (_: PrTerm)
  | PrApp (_: PrTerm) (_: PrTerm).


  Inductive Typ : Type :=
  | TpPi (_: Name) (_: Typ) (_: Typ)
  | TpApp (_: Typ) (_: Typ)
  | TpArrowT (_: Typ) (_: Typ)
  | TpVar (_: Var)
  | KdStar
  .

  Inductive Term : Type :=
  | VarT (_: Var)
  (* | RelT (_: nat) *)
  | LamT (_: Var) (_: option Typ) (_: Term)
  | AppT (_: Term) (_: Term)
  | ProdT (_: Name) (_: Term) (_: Term)
  .

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Typ).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * Typ).

  Inductive Data : Type :=
  | DefData (_: Var) (_: Params) (_: Typ) (_: Ctors).

  Inductive Assgn : Type :=
  | AssgnType (_: Var) (_: Typ)
  | AssgnTerm (_: Var) (_: Term)
  .

  Inductive Cmd : Type :=
  | CmdAssgn (_: Assgn)
  | CmdData (_: Data)
  .
Definition Program := list Cmd.
End Ced.
