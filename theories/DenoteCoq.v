Require Import Strings.String.
Require Import Strings.Ascii.
Require Import List. Import ListNotations.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
Require Import Hask.Data.List.
Require Import Hask.Data.Maybe.

Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.BasicAst.

Require Import Coquedille.Ast.

(* We use a default term instead of dealing with errors for now *)
Definition default_t x : Ced.Program := [Ced.CmdAssgn (Ced.AssgnTerm x (Ced.VarT x))].

(* I'm still not sure if the context should be a list Ced.Typ *)
(* Or a list Var *)
(* Because in theory the only thing the bruijn indices should refer *)
(* to would be Vars. *)
(* In fact I'm not sure if I should not be using de bruijn indices at all *)
Definition ctx := list Ced.Var.

Reserved Notation "⟦ x ⟧" (at level 0).


Definition DenoteName (n: name): Ced.Name :=
match n with
| nAnon => Ced.Anon
| nNamed c => Ced.Named c
end.

Fixpoint string_of_list_ascii (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons ch s => String ch (string_of_list_ascii s)
     end.

Fixpoint list_ascii_of_string (s : string) : list ascii
  := match s with
     | EmptyString => nil
     | String ch s => cons ch (list_ascii_of_string s)
     end.

Definition revStr (s: string) : string :=
string_of_list_ascii (rev (list_ascii_of_string s)).

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition kername_to_qualid (s: string): string :=
match index 0 "." (revStr s) with
| None => s
| Some n =>
  let s_len := String.length s in
  substring (s_len - n) s_len s
end.

Fixpoint denoteTerm (t: term) (genv : global_env) {struct t}: State ctx Ced.Typ :=
let default_name := Ced.TpVar "notimpl" in
match t with
  | tProd x t1 t2 =>
    t1' <- ⟦ t1 ⟧ genv ;
    Γ <- get ;
    match x with
    | nAnon =>
      put ("dummy" :: Γ) ;;
      t2'  <- ⟦ t2 ⟧ genv ;
      pure (Ced.TpArrowT t1' t2')
    | nNamed c =>
      put (c :: Γ) ;;
          t2'  <- ⟦ t2 ⟧ genv;
      pure (Ced.TpPi (Ced.Named c) t1' t2')
    end
  | tRel n =>
    Γ <- get ;
    match nth_error Γ n with
    | None => pure (Ced.TpVar "tERR")
    | Some x => pure (Ced.TpVar x)
    end
  | tApp t1 ts2 =>
    t1' <- ⟦ t1 ⟧ genv;
    Γ <- get ;
    let ts2' := map (fun t => fst (⟦ t ⟧ genv Γ)) ts2 in
    pure (fold_left (fun p1 p2 => Ced.TpApp p1 p2) ts2' t1')
  | tInd ind univ => pure (Ced.TpVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ =>
    (* Can we transform this to the Maybe Monad
       and then come back to the State Monad? *)
    (* Perhaps use Monad Transformers *)
    match lookup_mind_decl (inductive_mind ind) genv with
    | None => pure (Ced.TpVar "NoDecl")
    | Some d =>
      let bodies := ind_bodies d in
      match head bodies with
      | None => pure (Ced.TpVar "NoBody")
      | Some body =>
        let constrs := ind_ctors body in
        match nth_error constrs n with
        | None => pure (Ced.TpVar "NoConstr")
        | Some x =>
          let '(ctor, _, _) := x in pure (Ced.TpVar ctor)
        end
      end
    end
  | tSort univ => pure Ced.KdStar
  | _ => pure (Ced.TpVar "notimpl")
end
where "⟦ x ⟧" := (denoteTerm x).

Fixpoint removeBindings (t: term) (n: nat) : term :=
match n with
| O => t
| S n' =>
  match t with
  | tProd x t1 t2 => removeBindings t2 (pred n)
  | _ => t
  end
end.

Fixpoint denoteCtors (data_name : Ced.Var)
         (params: Ced.Params) (genv: global_env)
         (ctor: (ident * term) * nat) : Ced.Ctor  :=
let '(name, t, i) := ctor in
let v := data_name in
let paramnames := map fst params in
let clean_t := removeBindings t (length paramnames) in
let (t', _) := denoteTerm clean_t genv (rev (paramnames ,, v)) in
Ced.Ctr name t'.

Fixpoint denoteParams (genv : global_env) (params : context): Ced.Params :=
match params with
  | nil => []
  | cons p ps =>
    let name := decl_name p in
    let t := decl_type p in
    (match name with
     | nNamed n => [(n, fst (denoteTerm t genv [n]))]
     | cAnon => []
     end) ++ denoteParams genv ps
end.

(* Fixpoint get_ctx (gdecl: global_decl) : ctx := *)
(* match gdecl with *)
(* | ConstantDecl _ cbody => [cst_type cbody] *)
(* | InductiveDecl _ mbody => map ind_type (ind_bodies mbody) *)
(* end. *)

Instance List_Monad : Monad list :=
{ join := fun a l => fold_left (@app a) l [] }.

Fixpoint denoteGenv (genv: global_env) (e : global_decl) : Maybe Ced.Cmd :=
match e with
| InductiveDecl kern mbody =>
  body <- head (ind_bodies mbody) ;
  let name := ind_name body in
  let ctors := ind_ctors body in
  let params := rev (denoteParams genv (ind_params mbody)) in
  pure (Ced.CmdData (Ced.DefData name params Ced.KdStar (fmap (denoteCtors name params genv) ctors)))
| ConstantDecl _ _ => None
end.

Fixpoint maybeList {A} (x : Maybe A) : list A :=
match x with
| None => []
| Some a => [a]
end.

Fixpoint flattenMaybes {A} (x : list (Maybe A)) : list A :=
join (fmap maybeList x).

(* We assume that the term is well formed before calling denoteCoq *)
(* It's probably a good idea to add well formednes checker before calling it *)
(* TODO: browse metacoq library for well typed term guarantees *)
Fixpoint denoteCoq (p: program): Maybe Ced.Program :=
let (genv, t) := p in
match t with
| tInd ind univ =>
  (* let mind := inductive_mind ind in *)
  (* body <- lookup_mind_decl mind genv ; *)
  (* i_body <- head (ind_bodies body) ; *)
  (* let name := ind_name i_body in *)
  (* let ctors := ind_ctors i_body in *)
  (* let params := rev (denoteParams (ind_params body)) in *)
  (* let genv_terms := join (map get_terms genv) in *)
  (* let env : list Ced.Typ := map fst (map (fun f => denoteTerm f []) genv_terms) in *)
  (* pure [Ced.CmdData (Ced.DefData name params Ced.KdStar (fmap (denoteCtors name params) ctors))] *)

  (* Update this for denoteGenv only use the genvs seen so far *)
  let decls := flattenMaybes (fmap (denoteGenv genv) genv) in
  let t' := Ced.CmdAssgn (Ced.AssgnType "_" (fst (denoteTerm t genv []))) in
  pure (decls ++ [t'])
| _ => None
end.

Local Close Scope string_scope.
