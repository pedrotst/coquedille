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

  Fixpoint isKind (t: term): bool :=
  match t with
  | tSort _ => true
  | tProd _ t1 t2 => isKind t1 || isKind t2
  | _ => false
  end.


  Reserved Notation "⟦ x ⟧" (at level 0).
  Fixpoint denoteKind (t: term): m Ced.Kind :=
  match t with
  | tSort _ => ret Ced.KdStar
  | tProd x t1 t2 =>
    k1 <- (if isKind t1 then fmap inl (denoteKind t1) else fmap inr (denoteType t1)) ;;
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
    t2' <- local (fun '(genv, Γ) => (genv, ((binderName x) :: Γ))) (denoteType t2);;
    if isKind t1
    then
      k <- denoteKind t1 ;;
      ret (Ced.TyAll (denoteName x) k t2')
    else
      t1' <- denoteType t1 ;;
      ret (Ced.TyPi (denoteName x) t1' t2')
  | tApp t ts =>
    t' <- denoteType t ;;
       let den (t: term): m Ced.TTy :=
           match t with
           | tConstruct _ _ _ => fmap inr (denoteTerm t)
           | tApp _ _ => fmap inr (denoteTerm t)
           | _ => fmap inl (denoteType t)
           end in
    ts' <- list_m (map (fun t => den t) ts) ;;
    ret (Ced.TyApp t' ts')
  | tLambda x ty t =>
    ty' <- denoteType ty ;;
    t'  <- local (fun '(genv, Γ) => (genv, ((binderName x)) :: Γ)) (denoteType t) ;;
    ret (Ced.TyLam (denoteName x) ty' t')
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
  | tSort univ => ret (Ced.TyVar "tSort")
  end

  with denoteTerm (t: term): m Ced.Term :=
  match t with
  | tProd x t1 t2 => ret (Ced.TVar "tProd")
  | tSort univ => ret (Ced.TVar "tSort")
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) ("Variable " ++ utils.string_of_nat n ++ " not in environment");;
     ret (Ced.TVar v)
  | tApp t ts =>
    t' <- ⟦ t ⟧ ;;
    (* Have to fix this to check for term/type correctly *)
    ts' <- list_m (map (fun t => ⟦ t ⟧) ts) ;;
    ret (Ced.TApp t' (Ced.inj2List ts'))
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
  | tLambda x ty t =>
    ty' <- ⟦ ty ⟧ ;;
    t'  <- local (fun '(genv, Γ) => (genv, ((binderName x)) :: Γ)) ⟦ t ⟧ ;;
    ret (Ced.TLam (denoteName x) ty' t')
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

  (* Reserved Notation "⟦ x ⟧" (at level 0). *)
  (* Fixpoint denoteKind (t: term): m Ced.Term := *)
  (* match t with *)
  (* | tSort _ => ret Ced.KdStar *)
  (* | tProd x t1 t2 => *)
  (*   k1 <- (if isKind t1 then fmap inl (denoteKind t1) else fmap inr (denoteType t1)) ;; *)
  (*   k2 <-  denoteKind t2 ;; *)
  (*   ret (Ced.KdAll (denoteName x) k1 k2) *)
  (* | tRel n => *)
  (*   '(_, Γ) <- ask ;; *)
  (*    v <- option_m (nth_error Γ n) ("Variable " ++ utils.string_of_nat n ++ " not in environment");; *)
  (*    ret (Ced.TyVar v) *)
  (* | tProd x t1 t2 => *)
  (*   t2' <- local (fun '(genv, Γ) => (genv, ((binderName x) :: Γ))) (denoteType t2);; *)
  (*   if isKind t1 *)
  (*   then *)
  (*     k <- denoteKind t1 ;; *)
  (*     ret (Ced.TyAll (denoteName x) k t2') *)
  (*   else *)
  (*     t1' <- denoteType t1 ;; *)
  (*     ret (Ced.TyPi (denoteName x) t1' t2') *)
  (* | tApp t ts => *)
  (*   t' <- denoteType t ;; *)
  (*      let denote (t: term): m Ced.TTy := *)
  (*          if isType t *)
  (*          then fmap inl (denoteType t) *)
  (*          else fmap inr (denoteTerm t) in *)
  (*   ts' <- list_m (map (fun t => denote t) ts) ;; *)
  (*   ret (Ced.TyApp t' ts') *)
  (* | tLambda x ty t => *)
  (*   ty' <- denoteType ty ;; *)
  (*   t'  <- local (fun '(genv, Γ) => (genv, ((binderName x)) :: Γ)) (denoteType t) ;; *)
  (*   ret (Ced.TyLam (denoteName x) ty' t') *)
  (* | tInd ind univ => ret (Ced.TyVar (kername_to_qualid (inductive_mind ind))) *)
  (* | tConstruct ind n _ => raise "type tConstruct not implemented yet" *)
  (* | tVar _ => raise "type tVar not implemented yet" *)
  (* | tEvar _ _ => raise "type tEvar not implemented yet" *)
  (* | tFix _ _ => raise "type tFix not implemented yet" *)
  (* | tProj _ _ => raise "type tProj not implemented yet" *)
  (* | tCoFix _ _ => raise "type tCoFix not implemented yet" *)
  (* | tConst kern _ => ret (Ced.TyVar (kername_to_qualid kern)) *)
  (* | tCast _ _ _ => raise "type tCast not implemented yet" *)
  (* | tCase _ _ _ _ => raise "type tCase not implemented yet" *)
  (* | tLetIn _ _ _ _ => raise "type tLetIn not implemented yet" *)
  (* | tSort univ => ret (Ced.TyVar "tSort") *)
  (* end *)

  (* with denoteTerm (t: term): m Ced.Term := *)
  (* match t with *)
  (* | tProd x t1 t2 => ret (Ced.TVar "tProd") *)
  (* | tSort univ => ret (Ced.TVar "tSort") *)
  (* | tRel n => *)
  (*   '(_, Γ) <- ask ;; *)
  (*    v <- option_m (nth_error Γ n) ("Variable " ++ utils.string_of_nat n ++ " not in environment");; *)
  (*    ret (Ced.TVar v) *)
  (* | tApp t ts => *)
  (*   t' <- ⟦ t ⟧ ;; *)
  (*   (* Have to fix this to check for term/type correctly *) *)
  (*   ts' <- list_m (map (fun t => ⟦ t ⟧) ts) ;; *)
  (*   ret (Ced.TApp t' (Ced.inj2List ts')) *)
  (* | tInd ind univ => ret (Ced.TVar (kername_to_qualid (inductive_mind ind))) *)
  (* | tConstruct ind n _ => *)
  (*   '(genv, _) <- ask ;; *)
  (*   let minds := inductive_mind ind in *)
  (*   m_decl <- option_m (lookup_mind_decl minds genv) "Declaration not found" ;; *)
  (*   let bodies := ind_bodies m_decl in *)
  (*   body <- option_m (head bodies) "Could not find declaration body" ;; *)
  (*   let ctors := ind_ctors body in *)
  (*   '(ctor, _, _) <- option_m (nth_error ctors n) "Could not find constructor";; *)
  (*   ret (Ced.TVar ctor) *)
  (* | tLambda x ty t => *)
  (*   ty' <- ⟦ ty ⟧ ;; *)
  (*   t'  <- local (fun '(genv, Γ) => (genv, ((binderName x)) :: Γ)) ⟦ t ⟧ ;; *)
  (*   ret (Ced.TLam (denoteName x) ty' t') *)
  (* | tVar _ => raise "tVar not implemented yet" *)
  (* | tEvar _ _ => raise "tEvar not implemented yet" *)
  (* | tFix _ _ => raise "tFix not implemented yet" *)
  (* | tProj _ _ => raise "tProj not implemented yet" *)
  (* | tCoFix _ _ => raise "tCoFix not implemented yet" *)
  (* | tConst kern _ => ret (Ced.TVar (kername_to_qualid kern)) *)
  (* | tCast _ _ _ => raise "tCast not implemented yet" *)
  (* | tCase _ _ _ _ => raise "tCase not implemented yet" *)
  (* | tLetIn _ _ _ _ => raise "tLetIn not implemented yet" *)
  (* end *)
  (* where "⟦ x ⟧" := (denoteTerm x). *)

  Fixpoint removeBindings (t: Ced.Typ) (n: nat) : Ced.Typ :=
  match n with
  | O => t
  | S n' =>
    match t with
    | Ced.TyPi x t1 t2 => removeBindings t2 (pred n)
    | _ => t
    end
  end.

  Fixpoint removeBindingsTerm (t: term) (n: nat) : term :=
  match n with
  | O => t
  | S n' =>
    match t with
    | tProd x t1 t2 => removeBindingsTerm t2 (pred n)
    | _ => t
    end
  end.

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
    let name := get_ident (decl_name p) in
    let t := decl_type p in
    (* We may need a better way to tell if its a kind or type *)
    (* t' <- denoteType t ;; *)
    (* k' <- denoteKind t ;; *)
    tk <- (if isKind t then fmap inl (denoteKind t) else fmap inr (denoteType t)) ;;
    ls <- local (fun '(genv, Γ) => (genv, name :: Γ)) (denoteParams ps) ;;
    ret ((name, tk) :: ls)
  end.

  Definition denoteInductive mbody : m Ced.Cmd :=
  body <- option_m (head (ind_bodies mbody)) "Could not find body of definition" ;;
  let name := ind_name body in
  if String.eqb name "False"
  then ret (Ced.CmdAssgn (Ced.AssgnType "False" (Some Ced.KdStar) (Ced.TyAll (Ced.Named "X") Ced.KdStar (Ced.TyVar "X"))))
  else
    let ctors := ind_ctors body in
    params <- denoteParams (rev (ind_params mbody));;
    let full_ki := ind_type body in
    let noparam_ki := removeBindingsTerm full_ki (List.length params) in
    ki <- local (fun '(genv, _) => (genv, [name])) (denoteKind noparam_ki) ;;
    ctors' <- list_m (map (denoteCtors name (rev params)) ctors);;
    ret (Ced.CmdData (Ced.DefData name params ki ctors')).

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
      then ret ((Ced.CmdAssgn (Ced.AssgnTerm "False_ind" (Some (Ced.TyAll (Ced.Named "P") Ced.KdStar
                                                                       (Ced.TyPi Ced.Anon (Ced.TyVar "False")
                                                                                (Ced.TyVar "P"))))
                                            (Ced.TLamK (Ced.Named "P") Ced.KdStar (Ced.TLamT (Ced.Named "f") (Ced.TyPi Ced.Anon (Ced.TyVar "False") (Ced.TyVar "P")) (Ced.TApp (Ced.TVar "f") [inl (Ced.TyVar "P")]))))) :: ps)
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
   (* ty <- local (fun _ => (genv, [])) ⟦ t ⟧ ;; *)
   decls <- denoteGenv genv;;
   (* let t' := Ced.CmdAssgn (Ced.AssgnType "_" None ty) in *)
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
