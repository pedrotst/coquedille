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
Require Import ExtLib.Data.Map.FMapAList.

Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.BasicAst.

Require Import Coquedille.Ast.

Definition inj1M {A B mon} `{Monad mon} : mon A -> mon (sum A B) := fun m => fmap inl m.
Definition inj2M {A B mon} `{Monad mon} : mon B -> mon (sum A B) := fun m => fmap inr m.

Definition ctx := list Ced.Var.

Definition denoteName (n: name): Ced.Name :=
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
  Open Scope monad_scope.
  Open Scope string_scope.
  Open Scope list_scope.
  Notation "f ̊ g" := (fun x => f (g x)) (at level 80).


  Definition m A := readerT (global_env * ctx) (eitherT string IdentityMonad.ident) A.
  Definition run_m {A} (env: global_env * ctx) (ev: m A) := unIdent (unEitherT (runReaderT ev env)).
  Context {Monad_m : Monad m}.
  Context {Reader_m: MonadReader (global_env * ctx) m}.
  Context {Either_m: MonadExc string m}.


  Fixpoint list_m {A} {m': Type -> Type} `{Monad m'} (l : list (m' A)) : m' (list A) :=
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

  Definition kername_to_qualid (s: string): string :=
  match index 0 "." (revStr s) with
  | None => s
  | Some n =>
    let s_len := String.length s in
    substring (s_len - n) s_len s
  end.

  Fixpoint isKind (t: term): bool :=
  match t with
  | tSort _ => true
  | tProd _ t1 t2 => isKind t1 && isKind t2
  | _ => false
  end.

  Definition localDenote {A} (x: name) : m A -> m A :=
  local (fun '(genv, Γ) => (genv, (get_ident x) :: Γ)).

  Reserved Notation "⟦ x ⟧" (at level 9).
  Fixpoint denoteKind (t: term): m Ced.Kind :=
  match t with
  | tSort _ => ret Ced.KdStar
  | tProd x t1 t2 =>
    k1 <- (if isKind t1
         then fmap inl (localDenote x (denoteKind t1))
         else fmap inr (localDenote x (denoteType t1))) ;;
    k2 <-  denoteKind t2 ;;
    ret (Ced.KdAll (denoteName x) k1 k2)
  | _ => raise "Ill-formed kind"
  end
  with denoteType (t: term): m Ced.Typ :=
  match t with
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) ("Variable " ++ utils.string_of_nat n ++ " not in environment");;
     ret (Ced.TyVar v)
  | tProd x t1 t2 =>
    t2' <- localDenote x (denoteType t2) ;;
    if isKind t1
    then
      k <- denoteKind t1 ;;
      ret (Ced.TyAll (denoteName x) k t2')
    else
      t1' <- denoteType t1 ;;
      ret (Ced.TyPi (denoteName x) t1' t2')
  | tApp t ts =>
    t' <- denoteType t ;;
       let denApp (t: term) :=
           match t with
           | tConstruct _ _ _ | tApp _ _ =>
                                inj2M (denoteTerm t)
           | _ => inj1M (denoteType t)
           end in
    ts' <- list_m (map (fun t => denApp t) ts) ;;
    ret (Ced.TyApp t' ts')
  | tLambda x kty t =>
    t'  <- localDenote x (denoteType t) ;;
    if isKind kty
    then k <- denoteKind kty ;;
         ret (Ced.TyLamK (denoteName x) k t')
    else ty <- denoteType kty ;;
         ret (Ced.TyLam (denoteName x) ty t')
  | tInd ind univ => ret (Ced.TyVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ => raise "type tConstruct not implemented yet"
  | tVar _ => raise "type tVar not implemented yet"
  | tEvar _ _ => raise "type tEvar not implemented yet"
  | tFix _ _ => raise "type tFix not implemented yet"
  | tProj _ _ => raise "type tProj not implemented yet"
  | tCoFix _ _ => raise "type tCoFix not implemented yet"
  | tConst kern _ => ret (Ced.TyVar (kername_to_qualid kern))
  | tCast _ _ _ => raise "type tCast not implemented yet"
  | tCase _ _ _ _ => raise "type tCase not implemented yet"
  | tLetIn _ _ _ _ => raise "type tLetIn not implemented yet"
  | tSort univ => raise "type tSort not implemented yet"
  end

  with denoteTerm (t: term): m Ced.Term :=
  match t with
  | tProd x t1 t2 => ret (Ced.TVar "tProd")
  | tSort univ => ret (Ced.TVar "tSort")
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) ("Variable! " ++ utils.string_of_nat n ++ " not in environment");;
     ret (Ced.TVar v)
  | tApp t ts =>
    t' <- ⟦ t ⟧ ;;
    (* FIXME: We'll eventually have to actually check for term/type *)
    ts' <- list_m (map (fun t => ⟦ t ⟧) ts) ;;
    ret (Ced.TApp t' (inj2M ts'))
  | tInd ind univ => ret (Ced.TVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ =>
    '(genv, _) <- ask ;;
    let minds := inductive_mind ind in
    m_decl <- option_m (lookup_mind_decl minds genv) "Declaration not found" ;;
    let bodies := ind_bodies m_decl in
    body <- option_m (head bodies) "Could not find declaration body" ;;
    let ctors := ind_ctors body in
    '(ctor, _, _) <- option_m (nth_error ctors n) "Could not find constructor";;
    ret (Ced.TVar ctor)
  | tLambda x kty t =>
    t'  <- localDenote x ⟦ t ⟧ ;;
    if isKind kty
    then k <- denoteKind kty ;;
         ret (Ced.TLamK (denoteName x) k t')
    else ty <- denoteType kty ;;
         ret (Ced.TLam (denoteName x) false ty t')
  | tVar _ => raise "tVar not implemented yet"
  | tEvar _ _ => raise "tEvar not implemented yet"
  | tFix _ _ => raise "tFix not implemented yet"
  | tProj _ _ => raise "tProj not implemented yet"
  | tCoFix _ _ => raise "tCoFix not implemented yet"
  | tConst kern _ => ret (Ced.TVar (kername_to_qualid kern))
  | tCast _ _ _ => raise "tCast not implemented yet"
  | tCase _ _ _ _ => raise "tCase not implemented yet"
  | tLetIn _ _ _ _ => raise "tLetIn not implemented yet"
  end
  where "⟦ x ⟧" := (denoteTerm x).

  Fixpoint denoteCtors (data_name : Ced.Var)
           (params: Ced.Params)
           (ctor: (ident * term) * nat) : m Ced.Ctor  :=
  let '(name, t, i) := ctor in
  let paramnames := map fst params in
  t' <- local (fun '(genv, _) => (genv, [data_name])) (denoteType t) ;;
  ret (Ced.Ctr name t').

  Fixpoint denoteParams (params : context): m Ced.Params :=
  match params with
  | nil => ret []
  | cons p ps =>
    let x := decl_name p in
    let t := decl_type p in
    tk <- (if isKind t then inj1M (denoteKind t) else inj2M (denoteType t)) ;;
    ls <- localDenote x (denoteParams ps) ;;
    ret ((get_ident x, tk) :: ls)
  end.

  Definition denoteInductive mbody : m Ced.Cmd :=
  body <- option_m (head (ind_bodies mbody)) "Could not find body of definition" ;;
  let name := ind_name body in
  if String.eqb name "False"
  then ret (Ced.CmdAssgn (Ced.AssgnType "False" (Some Ced.KdStar) (Ced.TyAll (Ced.Named "X") Ced.KdStar (Ced.TyVar "X"))))
  else
    let ctors := ind_ctors body in
    let param_l := rev (ind_params mbody) in
    let param_names := map (get_ident ̊ decl_name) param_l in
    params <- denoteParams param_l;;
    let full_ki := ind_type body in
    let noparam_ki := remove_arity (List.length params) full_ki in
    ki <- local (fun '(genv, _) => (genv, param_names)) (denoteKind noparam_ki) ;;
    ctors' <- list_m (map (denoteCtors name (rev params)) ctors);;
    ret (Ced.CmdData (Ced.DefData name params ki ctors')).

  Definition False_ind_term : Ced.Assgn :=
  Ced.AssgnTerm "False_ind"
                (Some (Ced.TyAll
                         (Ced.Named "P")
                         Ced.KdStar
                         (Ced.TyPi Ced.Anon (Ced.TyVar "False")
                                   (Ced.TyVar "P"))))
                (Ced.TLamK (Ced.Named "P")
                           Ced.KdStar
                           (Ced.TLam (Ced.Named "f")
                                     false
                                     (Ced.TyPi Ced.Anon (Ced.TyVar "False")
                                               (Ced.TyVar "P"))
                                     (Ced.TApp (Ced.TVar "f")
                                               [inl (Ced.TyVar "P")]))).

  Fixpoint denoteGenv (es: global_env) : m Ced.Program :=
  match es with
  | nil => ret nil
  | e :: es' =>
    ps <- denoteGenv es';;
    match e with
    | InductiveDecl kern mbody =>
      p <- denoteInductive mbody ;;
      ret (p :: ps)
    | ConstantDecl kern cbody =>
      if (String.eqb kern "Coq.Init.Logic.False_ind")
      then ret ((Ced.CmdAssgn False_ind_term) :: ps)
      else
      bdy <- option_m (cst_body cbody) "Constant without a body" ;;
      let name := kername_to_qualid kern in
      if isKind (cst_type cbody)
      then ty <- denoteType bdy ;;
           k <- denoteKind (cst_type cbody)  ;;
           let asgn := Ced.CmdAssgn (Ced.AssgnType name (Some k) ty) in
           ret (asgn :: ps)
      else t <- ⟦ bdy ⟧;;
           ty <- denoteType (cst_type cbody) ;;
           let asgn := Ced.CmdAssgn (Ced.AssgnTerm name (Some ty) t) in
           ret (asgn :: ps)
    end
  end.

  (* We assume that the term is well formed before calling denoteCoq *)
  (* It's probably a good idea to add well formednes checker before calling it *)
  (* TODO: browse metacoq library for well typed term guarantees *)
  Fixpoint denoteCoq' (t: term): m Ced.Program :=
  (* TODO: Update this for denoteGenv only use the genvs seen so far *)
  '(genv, _) <- ask;;
   decls <- denoteGenv genv;;
   ret decls.

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

Definition denoteCoq (p: program) :=
let '(genv, t) := p in
run_m (genv, nil) (denoteCoq' t).
