Require Import String.
Require Import List. Import ListNotations.

Definition Var := string.

Inductive Name : Type :=
| cAnon
| cName (_: Var)
.

Inductive PrTerm : Type :=
| PrVar (_: nat)
| PrRef (_: Var)
| PrLam (_: PrTerm)
| PrApp (_: PrTerm) (_: PrTerm).

Inductive CedKind : Type :=
| KdStar
| KdArrow (_: CedKind) (_: CedKind)
| KdPi (_: CedKind) (_: CedKind).

Inductive CedType : Type :=
| TpPi (_: Name) (_: CedType) (_: CedType)
| TpAppTp (_: CedType) (_: CedType)
| TpAppTm (_: CedType) (_: PrTerm)
| TpArrowT (_: CedType) (_: CedType)
| TpVar (_: Var)
.

Inductive TpKd : Type :=
| TkKind (_: CedKind)
| TkType (_: CedType).


Inductive CedTerm : Type :=
| VarT (_: Var)
| LamT (_: Var) (_: option TpKd) (_: CedTerm)
| AppT (_: CedTerm) (_: CedTerm)
| ProdT (_: Name) (_: CedTerm) (_: CedTerm)
.

Inductive CedCtor : Type :=
| Ctr (_: Var) (_: CedType).

Definition CedCtors := list CedCtor.

Inductive CedData : Type :=
| DefData (_: Var) (_: CedKind) (_: CedCtors).

Inductive CedDef : Type :=
| DefType (_: Var) (_: CedType)
| DefTerm (_: Var) (_: CedTerm)
.

Inductive CedCmd : Type :=
| CmdDef (_: CedDef)
| CmdData (_: CedData)
.

Definition CedCmds := list CedCmd.
