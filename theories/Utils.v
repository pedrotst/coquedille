Require Import List. Import ListNotations.
Require Import String.

Require Import Coquedille.Ast.

Definition type_ctx := list (Ced.Var * Ced.Typ).

Fixpoint ctx_find (v : Ced.Var) (Γ : type_ctx) : option Ced.Typ :=
  match Γ with
  | nil => None
  | (v', ty) :: Γ' => if eqb v v'
                    then Some ty
                    else ctx_find v Γ'
  end.
