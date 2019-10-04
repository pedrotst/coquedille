Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.

Require Import Coquedille.Ast.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
Require Import Hask.Data.List.
Require Import Hask.Data.Maybe.
Require Import List. Import ListNotations.

(* We use a default term instead of dealing with errors for now *)
Definition default_t x := [CmdDef (DefTerm x (VarT x))].

Definition ced_context := list CedType.

Reserved Notation "⟦ x ⟧" (at level 0).

Definition nname_cname (n: name): Name :=
  match n with
  | nAnon => cAnon
  | nNamed c => cName c
  end.

Local Open Scope string_scope.

Fixpoint denoteTerm (t: term) {struct t}: State ced_context CedType :=
  let default_name := TpVar "NotImpl" in
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
    | None => return_ (TpVar "noty")
    | Some x => return_ x
    end
  | _ => pure default_name
  end
where "⟦ x ⟧" := (denoteTerm x).

Fixpoint denoteCtors (data_name : Var) (ctor: (ident * term) * nat): CedCtor  :=
  let '(name, t, i) := ctor in
  let '(t', Γ) := denoteTerm t [TpVar data_name] in
  Ctr name t'.

(* We assume that the term is well formed before calling denoteCoq *)
(* It's probably a good idea to add well formednes checker before calling it *)
(* TODO: browse metacoq library for well typed term guarantees *)
Fixpoint denoteCoq (p: program): Maybe CedProgram :=
  let (genv, t) := p in
  match t with
  | tInd ind univ =>
    let mind := inductive_mind ind in
    body <- lookup_mind_decl mind genv ;
    i_body <- head (ind_bodies body) ;
    let name := (ind_name i_body) in
    let ctors := ind_ctors i_body in
    pure [CmdData (DefData name KdStar (fmap (denoteCtors name) ctors))]
  | _ => None
  end.
