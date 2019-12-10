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

Section monadic.
  Local Open Scope monad_scope.
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Definition m A := readerT (global_env * ctx) (eitherT string IdentityMonad.ident) A.
  Definition run_m {A} (env: global_env * ctx) (ev: m A) := unIdent (unEitherT (runReaderT ev env)).
  Context {Monad_m : Monad m}.
  Context {Reader_m: MonadReader (global_env * ctx) m}.
  Context {Either_m: MonadExc string m}.

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

  Fixpoint list_m {A} (l : list (m A)) : m (list A) :=
  match l with
  | nil => ret nil
  | (x :: xs) =>
    x' <- x ;;
    xs' <- list_m xs ;;
    ret (x' :: xs')
  end.

  Definition option_m {A} (x : option A) s : m A :=
  match x with
  | None => raise s
  | Some y => ret y
  end.

  Fixpoint denoteTerm (t: term): m Ced.Typ :=
  let dummyTy := Ced.TpVar "dummyTy" in
  match t with
  | tProd x t1 t2 =>
    t1' <- ⟦ t1 ⟧ ;;
    t2' <- local (fun '(genv, Γ) => (genv, ((binderName x) :: Γ))) ⟦ t2 ⟧;;
    ret (Ced.TpPi (DenoteName x) t1' t2')
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) "Variable not in environment";;
     ret (Ced.TpVar v)
  | tApp t ts =>
    env <- ask ;;
    t' <- ⟦ t ⟧ ;;
    ts' <- list_m (map (fun t => ⟦ t ⟧) ts) ;;
    ret (Ced.TpApp t' ts')
  | tInd ind univ => ret (Ced.TpVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ =>
    '(genv, _) <- ask ;;
    let minds := inductive_mind ind in
    m_decl <- option_m (lookup_mind_decl minds genv) "Declaration not found" ;;
    let bodies := ind_bodies m_decl in
    body <- option_m (head bodies) "Could not find declaration body" ;;
    let ctors := ind_ctors body in
    '(ctor, _, _) <- option_m (nth_error ctors n) "Could not find constructor";;
    ret (Ced.TpVar ctor)
  | tSort univ => ret Ced.KdStar
  | _ => raise "Constructor not implemented yet"
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
           (params: Ced.Params)
           (ctor: (ident * term) * nat) : m Ced.Ctor  :=
  let '(name, t, i) := ctor in
  let v := data_name in
  let paramnames := map fst params in
  t' <- local (fun '(genv, _) => (genv, [v])) ⟦ t ⟧ ;;
  ret (Ced.Ctr name t').

  Fixpoint denoteParams (params : context): m Ced.Params :=
  match params with
  | nil => ret []
  | cons p ps =>
    let name := decl_name p in
    let t := decl_type p in
    ls <- denoteParams ps ;;
    head <- (match name with
            | nNamed n =>
              t' <- local id ⟦ t ⟧ ;;
              ret [(n, t')]
            | cAnon => ret []
            end) ;;
    ret (head ++ ls)
  end.

  Program Fixpoint denoteGenv (e : global_decl) : m Ced.Cmd :=
  match e with
  | InductiveDecl kern mbody =>
    body <- option_m (head (ind_bodies mbody)) "Could not find body of definition" ;;
    let name := ind_name body in
    let ctors := ind_ctors body in
    params <- denoteParams (ind_params mbody);;
    let full_ty := ind_type body in
    let noparam_ty := removeBindings full_ty (List.length (rev params)) in
    ty <- local (fun '(genv, _) => (genv, [])) ⟦ noparam_ty ⟧ ;;
    ctors' <- list_m (map (denoteCtors name params) ctors);;
    ret (Ced.CmdData (Ced.DefData name params ty ctors'))
  | ConstantDecl _ _ => raise "Only Inductives are implemented so far"
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
  Fixpoint denoteCoq' (p: program): m Ced.Program :=
  let (genv, t) := p in
  match t with
  | tInd ind univ =>
    (* TODO: Update this for denoteGenv only use the genvs seen so far *)
    decls <- list_m (map denoteGenv genv) ;;
    ty <- local (fun '(genv, _) => (genv, [])) ⟦ t ⟧ ;;
    let t' := Ced.CmdAssgn (Ced.AssgnType "_" ty) in
    ret (decls ++ [t'])
  | _ => raise "Kind of program not implemented"
  end.

  Local Close Scope string_scope.
  Local Close Scope monad_scope.

End monadic.

Instance m_Monad : Monad m.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadReader : MonadReader (global_env * ctx) m.
apply MonadReader_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadExc : MonadExc string m.
apply MonadExc_readerT.
apply Exception_eitherT.
apply Monad_ident.
Defined.

Definition denoteCoq p := run_m (nil, nil) (denoteCoq' p).
