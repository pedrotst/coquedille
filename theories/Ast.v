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
  | TyEq (_: Term) (_: Term)
  with Term : Type :=
  | TVar (_: Var)
  | TLam (_: Name) (erased: bool) (_: Typ) (_: Term)
  | TLamK (_: Name) (_: Kind) (_: Term)
  | TApp (_: Term) (_: list (Typ + Term))
  | TLetTm (_: Name) (erased: bool) (ty: Typ) (_: Term) (body: Term)
  | TLetTy (_: Name) (k: Kind) (ty: Typ) (body: Term)
  | TMu (is_rec: option Var) (_: Term) (_: option Typ) (branches: list (Term * Term))
  | TDelta (_ : Term)
  | TRho (lhs rhs : Term)
  | TBeta
  .
  Local Open Scope type_scope.

  Notation Sort := (Kind + Typ).
  Notation TyTerm := (Typ + Term).

  Inductive Ctor : Type :=
  | Ctr (_: Var) (_: Typ).

  Definition Ctors := list Ctor.

  Definition Params := list (Var * Sort).

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


(* Definition kind_is_sort : Ced.Kind -> Ced.Sort := inl. *)
(* Definition typ_is_sort : Ced.Typ -> Ced.Sort := inr. *)
(* Coercion kind_is_sort : Ced.Kind >-> Ced.Sort. *)
(* Coercion typ_is_sort : Ced.Typ >-> Ced.Sort. *)

(* Definition typ_is_tyterm : Ced.Typ -> Ced.TyTerm := inl. *)
(* Definition term_is_tyterm : Ced.Term -> Ced.TyTerm := inr. *)
(* Coercion typ_is_tyterm : Ced.Typ >-> Ced.TyTerm. *)
(* Coercion term_is_tyterm : Ced.Term >-> Ced.TyTerm. *)
