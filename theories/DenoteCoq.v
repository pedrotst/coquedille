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
Require Import MetaCoq.Template.utils.

Require Import Coquedille.Ast.

Definition inj1M {A B mon} `{Monad mon} : mon A -> mon (sum A B) := fun m => fmap inl m.
Definition inj2M {A B mon} `{Monad mon} : mon B -> mon (sum A B) := fun m => fmap inr m.

Definition ctx := list Ced.Var.


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

  Definition denoteName (n: name): Ced.Name :=
  match n with
  | nAnon => Ced.Anon
  | nNamed c => Ced.Named c
  end.

  Definition getName (n: Ced.Name): Ced.Var :=
  match n with
  | Ced.Anon => "_"
  | Ced.Named c => c
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

  (* TODO: Implement a smarter technique to deal with name desambiguation *)
  (* The whole problem comes down to the fact that metacoq can clash binder names *)
  (* with datatypes. (Check the example t_isnil without this _ hack) *)
  (* My idea to solve this more elegantly is to put the full name in the env *)
  (* And perform lookup on kername_to_qualid *)
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
  | tProd _ t1 t2 => isKind t2
  | _ => false
  end.

  Fixpoint lookup_constant (id : ident) (decls : global_env)
    := match decls with
       | nil => None
       | ConstantDecl kn d :: tl =>
         if String.eqb kn id then Some d else lookup_constant id tl
       | _ :: tl => lookup_constant id tl
       end.

  Fixpoint isType (t: term) : m bool :=
  '(genv, Γ) <- ask ;;
   match t with
   | tInd _ _ => ret true
   | tProd _ t1 t2 =>
     b1 <- isType t1 ;;
     b2 <- isType t2 ;;
     ret (andb b1 b2)
   | tConst kern _ =>
     (* let cdecl := lookup_constant kern genv in *)
     cdecl <- option_m (lookup_constant kern genv) "Couldn't find cdecl body" ;;
     let cdecl_ty := (cst_type cdecl) in
     ret (isKind cdecl_ty)
   | tApp t _ => isType t
   | _ => ret false
   end.

  Fixpoint decl_exists (id : ident) (decls : global_env) : bool :=
  match decls with
  | [] => false
  | ConstantDecl kn d :: tl =>
      match string_compare (kername_to_qualid kn) id with
      | Eq => true
      | _ => decl_exists id tl
      end
  | InductiveDecl kn d :: tl =>
      match string_compare (kername_to_qualid kn) id with
      | Eq => true
      | _ => decl_exists id tl
      end
  end.

  Definition fresh (x: ident) : m ident :=
  '(genv, _) <- ask ;;
  if (decl_exists x genv)
  (* TODO: Implement a smarter / nicer fresh generator *)
  then ret (append x "'")
  else ret x.

  Definition localDenote {A} (x: name) (r: m A): m (A * Ced.Name):=
  match x with
  | nAnon =>
    r' <- local (fun '(genv, Γ) => (genv, "_" :: Γ)) r ;;
    ret (r', Ced.Anon)
  | nNamed n =>
    x' <- fresh n ;;
    r' <- local (fun '(genv, Γ) => (genv, x' :: Γ)) r ;;
    ret (r' , Ced.Named x')
  end.

  Fixpoint take_args' (acc: list (Ced.Typ + Ced.Term)) (n : nat) (t: term)
    : m (list (Ced.Typ + Ced.Term)) :=
  match n with
  | O => ret acc
  | S n' =>
    match t with
    | tLambda x ty t' =>
      x' <- fresh (get_ident x) ;;
      b <- isType ty ;;
      if b
      then take_args' (inl (Ced.TyVar x') :: acc) n' t'
      else take_args' (inr (Ced.TVar x') :: acc) n' t'
    | _ => ret acc
    end
  end.

  Definition ctor_typ := ((ident × term) × nat).

  Definition take_args (brch : nat * term) :=
  let '(nargs, t) := brch in
  args <- take_args' nil nargs t;;
  ret (rev args).

  Definition get_ctors ind : m (list (ident * term * nat)) :=
    '(genv, _) <- ask ;;
    let minds := inductive_mind ind in
    m_decl <- option_m (lookup_mind_decl minds genv) "Declaration not found" ;;
    let bodies := ind_bodies m_decl in
    body <- option_m (head bodies) "Could not find declaration body" ;;
    ret (ind_ctors body).

  Definition build_tApp (nts: ctor_typ * list (Ced.Typ + Ced.Term)) :=
  let '(ctor, ts) := nts in
  let '(n, _, _) := ctor in
  Ced.TApp (Ced.TVar n) ts.

  Definition get_ctor_name : ident * term * nat -> ident :=
  fun x => fst (fst x).


  Fixpoint removeLambdas (n: nat) (t: Ced.Term) :=
  match n with
  | O => t
  | S n' =>
    match t with
    | Ced.TLamK _ _ t' | Ced.TLam _ _ _ t' => removeLambdas n' t'
    | _ => t
    end
  end.

  Fixpoint showList' (ls : list string) : string :=
  match ls with
  | nil => ""
  | cons x xs => x ++ ", " ++ showList' xs
  end.

  Fixpoint showList (ls : list string) : string :=
  "[ " ++ showList' ls ++ "]".

(* (tLetIn (nNamed "H0"%string) *)
(*         (tApp *)
(*            (tConst *)
(*               "Coq.Init.Logic.eq_ind"%string *)
(*               []) *)
(*            [tInd *)
(*               {| *)
(*                 inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                 inductive_ind := 0 |} []; *)
(*             tConstruct *)
(*               {| *)
(*                 inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                 inductive_ind := 0 |} 0 []; *)
(*             tLambda (nNamed "e"%string) *)
(*                     (tInd *)
(*                        {| *)
(*                          inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                          inductive_ind := 0 |} []) *)
(*                     (tCase *)
(*                        ({| *)
(*                            inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                            inductive_ind := 0 |}, 0) *)
(*                        (tLambda  *)
(*                           (nNamed "n"%string) *)
(*                           (tInd *)
(*                              {| *)
(*                                inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                inductive_ind := 0 |} []) *)
(*                           (tSort *)
(*                              (Universe.make'' *)
(*                                 (Level.lProp, false) []))) *)
(*                        (tRel 0) *)
(*                        [(0, *)
(*                          tInd *)
(*                            {| *)
(*                              inductive_mind := "Coq.Init.Logic.True"; *)
(*                              inductive_ind := 0 |} []); *)
(*                         (1, *)
(*                          tLambda nAnon *)
(*                                  (tInd *)
(*                                     {| *)
(*                                       inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                                       inductive_ind := 0 |} []) *)
(*                                  (tInd *)
(*                                     {| *)
(*                                       inductive_mind := "Coq.Init.Logic.False"; *)
(*                                       inductive_ind := 0 |} []))]); *)
(*             tConstruct *)
(*               {| *)
(*                 inductive_mind := "Coq.Init.Logic.True"; *)
(*                 inductive_ind := 0 |} 0 []; *)
(*             tApp *)
(*               (tConstruct *)
(*                  {| *)
(*                    inductive_mind := "Coq.Init.Datatypes.nat"; *)
(*                    inductive_ind := 0 |} 1 []) *)
(*               [tRel 1];  *)
(*             tRel 0]) *)
(*         (tInd *)
(*            {| *)
(*              inductive_mind := "Coq.Init.Logic.False"; *)
(*              inductive_ind := 0 |} []) *)
(*         (tApp *)
(*            (tConst *)
(*               "Coq.Init.Logic.False_ind"%string *)
(*               []) *)
(*            [tInd *)
(*               {| *)
(*                 inductive_mind := "Coq.Init.Logic.False"; *)
(*                 inductive_ind := 0 |} []; *)
(*             tRel 0])) *)

  (* Next step is to build the delta term *)
  (* in order to do this it is necessary to denote part of the term *)
  (* to figure out the name of the variables building the equality *)
  Definition defaultK : Ced.Kind := Ced.KdStar.
  Definition defaultTy : Ced.Typ := Ced.TyVar "xx".
  Definition defaultTer : Ced.Term := Ced.TVar "xx".

  Definition is_delta (t: term) : bool :=
  match t with
  | tLetIn v t' kty bdy =>
    match kty with
    | tInd s _ =>
      if String.eqb "Coq.Init.Logic.False" (inductive_mind s)
      then match t' with
           | tApp (tConst s' _) _ =>
             if String.eqb "Coq.Init.Logic.eq_ind" s'
             then true
             else false
           | _ => true
           end
      else false

    | _ => false
    end
  | _ => false
  end.

  (* | TMu (is_rec: bool) (_: Term) (_: option Typ)
     (branches: list (Term * Term)) *)

(* (μ' e @ (λ x : nat . λ _ : eq ·nat (S n) x . { S n ≃ x }) *)
         (* { eq_refl ➔ β } ) *)
  (* | TLam (_: Name) (erased: bool) (_: Typ) (_: Term) *)
  Definition eq_elim (eq: Ced.Term) (eqty : Ced.Typ) (y: Ced.Term): Ced.Term :=
  Ced.TMu false eq
          (Some
             (Ced.TyLam
                (Ced.Named "x")
                eqty
                (Ced.TyLam
                   Ced.Anon
                   (Ced.TyApp
                      (Ced.TyVar "eq")
                      [inl eqty ;
                       inr y;
                       inr (Ced.TVar "x")])
                   (Ced.TyEq y (Ced.TVar "x")))
             )
          )
          [(Ced.TVar "eq_refl", Ced.TBeta)].

  Reserved Notation "⟦ x ⟧" (at level 9).
  Fixpoint denoteKind (t: term): m Ced.Kind :=
  match t with
  | tSort _ => ret Ced.KdStar
  | tProd x t1 t2 =>
    k1 <- (if isKind t1
         then fmap inl (denoteKind t1)
         else fmap inr (denoteType t1)) ;;
    '(k2, x') <-  localDenote x (denoteKind t2) ;;
    ret (Ced.KdAll x' k1 k2)
  | _ => raise "Ill-formed kind"
  end
  with denoteType (t: term): m Ced.Typ :=
  match t with
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) ("ty tRel " ++ utils.string_of_nat n ++ " not in environment " ++ showList Γ);;
     ret (Ced.TyVar v)
  | tProd x t1 t2 =>
    '(t2', x') <- localDenote x (denoteType t2) ;;
    if isKind t1
    then
      k <- denoteKind t1 ;;
      ret (Ced.TyAll x' k t2')
    else
      t1' <- denoteType t1 ;;
      ret (Ced.TyPi x' t1' t2')
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
    '(t', x') <- localDenote x (denoteType t) ;;
    if isKind kty
    then k <- denoteKind kty ;;
         ret (Ced.TyLamK x' k t')
    else ty <- denoteType kty ;;
         ret (Ced.TyLam x' ty t')
  | tInd ind univ => ret (Ced.TyVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ => raise "type tConstruct not implemented yet"
  | tVar _ => raise "type tVar not implemented yet"
  | tEvar _ _ => raise "type tEvar not implemented yet"
  | tFix _ _ => raise "type tFix not implemented yet"
  | tProj _ _ => raise "type tProj not implemented yet"
  | tCoFix _ _ => raise "type tCoFix not implemented yet"
  | tConst kern _ => ret (Ced.TyVar (kername_to_qualid kern))
  | tCast t _ _ => denoteType t
  | tCase _ _ _ _ => raise "type tCase not implemented yet"
  | tLetIn _ _ _ _ => raise "type tLetIn not implemented yet"
  | tSort univ => ret defaultTy
    (* raise "type tSort not implemented yet" *)
  end

  with denoteTerm (t: term): m Ced.Term :=
  match t with
  | tProd x t1 t2 => ret (Ced.TVar "tProd")
  | tSort univ => ret (Ced.TVar "tSort")
  | tRel n =>
    '(_, Γ) <- ask ;;
     v <- option_m (nth_error Γ n) ("term Variable " ++ utils.string_of_nat n ++ " not in environment");;
     ret (Ced.TVar v)
  | tApp t ts =>
    t' <- ⟦ t ⟧ ;;
    ts' <- list_m (map (fun e => b <- isType e ;;
                             if b
                             then fmap inl (denoteType e)
                             else fmap inr (denoteTerm e))
                      ts) ;;
    ret (Ced.TApp t' ts')
  | tInd ind univ => ret (Ced.TVar (kername_to_qualid (inductive_mind ind)))
  | tConstruct ind n _ =>
    ctors <- get_ctors ind ;;
    '(ctor, _, _) <- option_m (nth_error ctors n) "Could not find constructor";;
    ret (Ced.TVar ctor)
  | tLambda x kty t =>
    '(t', x') <- localDenote x ⟦ t ⟧ ;;
    if isKind kty
    then k <- denoteKind kty ;;
         ret (Ced.TLamK x' k t')
    else ty <- denoteType kty ;;
         ret (Ced.TLam x' false ty t')
  | tLetIn x t' kty bdy =>
    if is_delta t
    then
      t'' <- denoteTerm t' ;;
      match t'' with
      | Ced.TApp _ ([(inl eqty); (inr x); _; _; (inr y); (inr eq)]) =>
        ret (Ced.TDelta (eq_elim eq eqty x))
      | Ced.TApp _ ([(inr eqty); (inr x); _; _; (inr y); (inr eq)]) =>
        ret (Ced.TVar "got eqterm")
      | _ => ret (Ced.TVar "delwrong")
        (* raise "something went wrong translating delta" *)
      end
    else
      '(bdy', x') <- localDenote x ⟦ bdy ⟧ ;;
      if isKind kty
      then k <- denoteKind kty ;;
           t'' <- denoteType t' ;;
           ret (Ced.TLetTy x' k t'' bdy')
      else ty <- denoteType kty ;;
           t'' <- denoteTerm t' ;;
           ret (Ced.TLetTm x' false ty t'' bdy')
  | tVar _ => raise "tVar not implemented yet"
  | tEvar _ _ => raise "tEvar not implemented yet"
  | tFix _ _ => raise "tFix not implemented yet"
  | tProj _ _ => raise "tProj not implemented yet"
  | tCoFix _ _ => raise "tCoFix not implemented yet"
  | tConst kern _ => ret (Ced.TVar (kername_to_qualid kern))
  | tCast t _ _ => ⟦ t ⟧
  | tCase (ind, npars) mot c brchs =>
    ctors <- get_ctors ind ;;
    c' <- ⟦ c ⟧ ;;
    args <- list_m (map take_args brchs) ;;
    ts' <- list_m (map (fun '(_, t) => denoteTerm t) brchs) ;;
    let trimmed_ts' := map (fun '(n, t) => removeLambdas n t) (combine (map fst brchs) ts') in
    let constrs := map build_tApp (combine ctors args) in
    ret (Ced.TMu false c' None (combine constrs trimmed_ts'))
                 (* (combine constrs ts')) *)
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
    '(ls, x') <- localDenote x (denoteParams ps) ;;
    ret ((getName x', tk) :: ls)
  end.


  Definition denoteInductive mbody : m Ced.Cmd :=
  body <- option_m (head (ind_bodies mbody)) "Could not find body of definition" ;;
  let name := ind_name body in
  (* let name := kername_to_qualid n in *)
  if String.eqb name "False"
  then ret (Ced.CmdAssgn (Ced.AssgnType "False" (Some Ced.KdStar) (Ced.TyAll (Ced.Named "X") Ced.KdStar (Ced.TyVar "X"))))
  else
    let ctors := ind_ctors body in
    let param_l := rev (ind_params mbody) in
    let param_names := map (get_ident ̊ decl_name) param_l in
    params <- denoteParams param_l;;
    let tki := ind_type body in
    ki <- local (fun '(genv, _) => (genv, param_names)) (denoteKind tki) ;;
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
                                     (Ced.TyVar "False")
                                     (Ced.TApp (Ced.TVar "f")
                                               [inl (Ced.TyVar "P")]))).

  (* JMeq_rect : ∀ A : ★ . Π x : A . ∀ P : A ➔ ★ . P x ➔ Π y : A .
JMeq_ ·A x ·A y ➔ P y *)
  (* = Λ A . λ x . Λ P . λ p . λ y . λ j . *)
  (* μ' j @(λ A1 : ★ . λ y1 : A1 . λ _ : JMeq_ ·A x ·A1 y1 . P y){ *)
  (* | JMeq_refl ➔ [H : { y ≃ x } = μ' j { JMeq_refl ➔ β } ] *)
  (* - ρ H - p *)
  (* }. *)

  Definition JMeq_rect_term : Ced.Assgn :=
           (Ced.AssgnTerm "JMeq_rect"
              (Some
                 (Ced.TyAll (Ced.Named "A") Ced.KdStar
                    (Ced.TyPi (Ced.Named "x")
                       (Ced.TyVar "A")
                       (Ced.TyAll (Ced.Named "P")
                          (Ced.KdAll Ced.Anon
                             (inr (Ced.TyVar "A"))
                             Ced.KdStar)
                          (Ced.TyPi Ced.Anon
                             (Ced.TyApp
                                (Ced.TyVar "P")
                                [inl (Ced.TyVar "x")])
                             (Ced.TyPi
                                (Ced.Named "y")
                                (Ced.TyVar "A")
                                (Ced.TyPi
                                   (Ced.Anon)
                                   (Ced.TyApp
                                      (Ced.TyVar "JMeq")
                                      [
                                      inl (Ced.TyVar "A");
                                      inl (Ced.TyVar "x");
                                      inl (Ced.TyVar "A");
                                      inl (Ced.TyVar "y")])
                                   (Ced.TyApp
                                      (Ced.TyVar "P")
                                      [inl (Ced.TyVar "y")]
                                   )
              )))))))
              (Ced.TLamK (Ced.Named "A") Ced.KdStar
                 (Ced.TLam (Ced.Named "x") false
                    (Ced.TyVar "A")
                    (Ced.TLamK (Ced.Named "P")
                       (Ced.KdAll Ced.Anon
                          (inr (Ced.TyVar "A")) Ced.KdStar)
                       (Ced.TLam (Ced.Named "p") false
                          (Ced.TyApp (Ced.TyVar "P")
                             [inl (Ced.TyVar "x")])
                          (Ced.TLam (Ced.Named "y") false
                             (Ced.TyVar "A")
                             (Ced.TLam
                                (Ced.Named "H") false
                                (Ced.TyApp
                                   (Ced.TyVar "JMeq")
                                   [inl (Ced.TyVar "A");
                                   inl (Ced.TyVar "x");
                                   inl (Ced.TyVar "A");
                                   inl (Ced.TyVar "y")])
                                (Ced.TMu
                                   false
                                   (Ced.TVar "H")
                                   (Some (Ced.TyLamK
                                            (Ced.Named "A1")
                                            Ced.KdStar
                                            (Ced.TyLam
                                               (Ced.Named "y1")
                                               (Ced.TyVar "A1")
                                               (Ced.TyLam
                                                  Ced.Anon
                                                  (Ced.TyApp
                                                     (Ced.TyVar "JMeq")
                                                     [inl (Ced.TyVar "A");
                                                      inl (Ced.TyVar "x");
                                                      inl (Ced.TyVar "A1");
                                                      inl (Ced.TyVar "y1")
                                                  ])
                                                  (Ced.TyApp
                                                     (Ced.TyVar "P")
                                                     [inl (Ced.TyVar "y")])
                                            ))))
                                   [(Ced.TVar "JMeq_refl",
                                     Ced.TLetTm
                                       (Ced.Named "H")
                                       false
                                       (Ced.TyEq
                                          (Ced.TVar "y")
                                          (Ced.TVar "x"))
                                       (Ced.TMu
                                          false
                                          (Ced.TVar "H")
                                          None
                                          [(Ced.TVar "JMeq_refl",
                                            Ced.TBeta
                                          )]
                                       )
                                       (Ced.TRho
                                          (Ced.TVar "H")
                                          (Ced.TVar "p")
                                       )
                                )])
           ))))))).

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
      if (String.eqb kern
                     "Coq.Init.Logic.False_ind")
      then ret ((Ced.CmdAssgn False_ind_term) :: ps)
      else
      if (String.eqb kern "Coq.Logic.JMeq.JMeq_rect")
      then ret ((Ced.CmdAssgn JMeq_rect_term) :: ps)
      else
        (* Ignore JMeq_eq because it is an axiom *)
        (* TODO: Find better ways to deal with axioms *)
      if (String.eqb kern "Coq.Logic.JMeq.JMeq_eq")
      then ret ps
      else
      bdy <- option_m (cst_body cbody) ("Constant " ++ kern ++ " does not have a body defined") ;;
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
