Require Import String.
Require Import List. Import ListNotations.

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

Inductive Kind : Type :=
| KdStar
| KdArrow (_: Kind) (_: Kind)
| KdPi (_: Kind) (_: Kind).

Inductive Typ : Type :=
| TpPi (_: Name) (_: Typ) (_: Typ)
| TpAppTp (_: Typ) (_: Typ)
| TpAppTm (_: Typ) (_: PrTerm)
| TpArrowT (_: Typ) (_: Typ)
| TpVar (_: Var)
.

Inductive TpKd : Type :=
| TkKind (_: Kind)
| TkType (_: Typ).


Inductive Term : Type :=
| VarT (_: Var)
(* | RelT (_: nat) *)
| LamT (_: Var) (_: option TpKd) (_: Term)
| AppT (_: Term) (_: Term)
| ProdT (_: Name) (_: Term) (_: Term)
.

Inductive Ctor : Type :=
| Ctr (_: Var) (_: Typ).

Definition Ctors := list Ctor.

Inductive Data : Type :=
| DefData (_: Var) (_: Kind) (_: Ctors).

Inductive Assgn : Type :=
| AssgnType (_: Var) (_: Typ)
| AssgnTerm (_: Var) (_: Term)
.

Inductive Cmd : Type :=
| CmdAssgn (_: Assgn)
| CmdData (_: Data)
.

Definition Program := list Cmd.