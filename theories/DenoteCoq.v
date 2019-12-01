Require Import Strings.String.
Require Import Strings.Ascii.
Require Import List. Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Import MonadNotation.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.ListMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.ContMonad.

Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.BasicAst.

Require Import Coquedille.Ast.
Require Import Coquedille.Utils.

(* We use a default term instead of dealing with errors for now *)
Definition default_t x : Ced.Program := [Ced.CmdAssgn (Ced.AssgnTerm x (Ced.VarT x))].

(* I'm still not sure if the context should be a list Ced.Typ *)
(* Or a list Var *)
(* Because in theory the only thing the bruijn indices should refer *)
(* to would be Vars. *)
(* In fact I'm not sure if I should not be using de bruijn indices at all *)
Definition ctx := list (Ced.Var).

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

Definition binderName (x : name) : Ced.Var :=
match x with
| nAnon => "anon"
| nNamed name => name
end.

Section monad.
Local Open Scope monad_scope.

Section monadic.

Definition m A := readerT (global_env * ctx) (eitherT string IdentityMonad.ident) A.
Definition run_m {A} (env: global_env * ctx) (ev: m A) := unIdent (unEitherT (runReaderT ev env)).
Context {Monad_m : Monad m}.
Context {Reader_m: MonadReader (global_env * ctx) m}.
Context {Either_m: MonadExc string m}.
(* Context {Maybe_m : MonadMaybe m}. *)

Definition find_err {A B C} (l: list A) (find: list A -> option C)  err (f: C -> B)  : m B :=
match find l with
| None => raise err
| Some x => ret (f x)
end.

Fixpoint mapErr {A B} (l : list (A + B)) : A + list B :=
match l with
| nil => inr nil
| (inl x :: xs) => inl x
| (inr x :: xs) =>
  xs' <- mapErr xs ;;
  ret (x :: xs')
end.

Definition join `{M : Monad m} {A: Type} (mon: m (m A)) : m A :=
mon >>= id.

Fixpoint denoteTerm (t: term) {struct t}: m Ced.Typ :=
let dummyTy := Ced.TpVar "dummyTy" in
match t with
  | tProd x t1 t2 =>
    t1' <- ⟦ t1 ⟧ ;;
    t2' <- local (fun '(genv, Γ) => (genv, ((binderName x) :: Γ))) ⟦ t2 ⟧;;
    ret (Ced.TpPi (DenoteName x) t1' t2')
  | tRel n =>
    '(_, Γ) <- ask ;;
     t <- find_err Γ (fun g => nth_error g n) "variable not in environment" Ced.TpVar;;
     ret t
  | tApp t1 ts2 =>
    env <- ask ;;
    t1' <- ⟦ t1 ⟧ ;;
    let ts2' := map (fun t => (run_m env ⟦ t ⟧)) ts2 in
    match mapErr ts2' with
    | inl s => raise s
    | inr ts => ret (Ced.TpApp t1' ts)
    end
  | tInd ind univ => ret (Ced.TpVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ =>
    '(genv, _) <- ask ;;
     t <- (join (join (find_err genv (fun g => lookup_mind_decl (inductive_mind ind) g) "variable not in environment"
       (fun d => find_err (ind_bodies d) (@head _) "Could not find declaration body"
          (fun bodies => find_err (ind_ctors bodies) (fun c => nth_error c n) "Could not find constructor"
            (fun '(ctor, _, _) => Ced.TpVar ctor
       )))))) ;;
       ret t
  | tSort univ => ret Ced.KdStar
  | _ => raise "Constructor not implemented yet"
end
where "⟦ x ⟧" := (denoteTerm x).

End monadic.

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
let t' := evalState (denoteTerm t genv) [v] in
Ced.Ctr name t'.

Fixpoint denoteParams (genv : global_env) (params : context): Ced.Params :=
match params with
  | nil => []
  | cons p ps =>
    let name := decl_name p in
    let t := decl_type p in
    (match name with
     | nNamed n => [(n, evalState (denoteTerm t genv) [n])]
     | cAnon => []
     end) ++ denoteParams genv ps
end.

(* Instance List_Monad : Monad list := *)
(* { join := fun a l => fold_left (@app a) l [] }. *)

Fixpoint denoteGenv (genv: global_env) (e : global_decl) : option Ced.Cmd :=
match e with
| InductiveDecl kern mbody =>
  body <- head (ind_bodies mbody) ;;
  let name := ind_name body in
  let ctors := ind_ctors body in
  let params := rev (denoteParams genv (ind_params mbody)) in
  let full_ty := ind_type body in
  let noparam_ty := removeBindings full_ty (List.length params) in
  let ty := evalState (denoteTerm noparam_ty genv) [] in
  ret (Ced.CmdData (Ced.DefData name params ty (fmap (denoteCtors name params genv) ctors)))
| ConstantDecl _ _ => None
end.

Fixpoint maybeList {A} (x : option A) : list A :=
match x with
| None => []
| Some a => [a]
end.

Fixpoint flattenMaybes {A} (x : list (option A)) : list A :=
fold_left (@app A) (fmap maybeList x) [].

(* We assume that the term is well formed before calling denoteCoq *)
(* It's probably a good idea to add well formednes checker before calling it *)
(* TODO: browse metacoq library for well typed term guarantees *)
Fixpoint denoteCoq (p: program): option Ced.Program :=
let (genv, t) := p in
match t with
| tInd ind univ =>
  (* Update this for denoteGenv only use the genvs seen so far *)
  let decls := flattenMaybes (fmap (denoteGenv genv) genv) in
  let t' := Ced.CmdAssgn (Ced.AssgnType "_" (evalState (denoteTerm t genv) [])) in
  pure (decls ++ [t'])
| _ => None
end.

Local Close Scope string_scope.
Local Close Scope monad_scope.
