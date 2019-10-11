Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
Require Import Hask.Data.List.
Require Import Hask.Data.Maybe.
Require Import List. Import ListNotations.

Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.BasicAst.

Require Import Coquedille.Ast.

(* We use a default term instead of dealing with errors for now *)
Definition default_t x : Ced.Program := [Ced.CmdAssgn (Ced.AssgnTerm x (Ced.VarT x))].

Definition ctx := list Ced.Typ.

Reserved Notation "⟦ x ⟧" (at level 0).

Definition nname_cname (n: name): Ced.Name :=
  match n with
  | nAnon => Ced.Anon
  | nNamed c => Ced.Named c
  end.

Local Open Scope string_scope.

Fixpoint denoteTerm (t: term) {struct t}: State ctx Ced.Typ :=
  let default_name := Ced.TpVar "notimpl" in
  match t with
  | tProd x t1 t2 =>
    t1' <- ⟦ t1 ⟧ ;
    Γ <- get ;
    put (Γ ,, t1') ;;
    t2'  <- ⟦ t2 ⟧ ;
    let cname := nname_cname x in
    pure (Ced.TpPi cname t1' t2')
  | tRel n =>
    Γ <- get ;
    match nth_error Γ n with
    | None => pure (Ced.TpVar "typing err")
    | Some x => pure x
    end
  | _ => pure default_name
  end
where "⟦ x ⟧" := (denoteTerm x).

Fixpoint denoteCtors (data_name : Ced.Var) (ctor: (ident * term) * nat): Ced.Ctor  :=
  let '(name, t, i) := ctor in
  let '(t', Γ) := denoteTerm t [Ced.TpVar data_name] in
  Ced.Ctr name t'.

(* We assume that the term is well formed before calling denoteCoq *)
(* It's probably a good idea to add well formednes checker before calling it *)
(* TODO: browse metacoq library for well typed term guarantees *)
Fixpoint denoteCoq (p: program): Maybe Ced.Program :=
  let (genv, t) := p in
  match t with
  | tInd ind univ =>
    let mind := inductive_mind ind in
    body <- lookup_mind_decl mind genv ;
    i_body <- head (ind_bodies body) ;
    let name := (ind_name i_body) in
    let ctors := ind_ctors i_body in
    pure [Ced.CmdData (Ced.DefData name Ced.KdStar (fmap (denoteCtors name) ctors))]
  | _ => None
  end.
