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
Require Import Coquedille.Hardcoded.

Definition inj1M {A B mon} `{Monad mon} : mon A -> mon (sum A B) := fun m => fmap inl m.
Definition inj2M {A B mon} `{Monad mon} : mon B -> mon (sum A B) := fun m => fmap inr m.

Definition ctx := list Ced.Var.

Local Definition string_eq x y := utils.string_compare x y = Eq.

Local Instance string_RelDec : RelDec.RelDec string_eq :=
  { rel_dec := String.eqb }.

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
  Open Scope bool_scope.
  Open Scope type_scope.
  Notation "f ̊ g" := (fun x => f (g x)) (at level 80).

  (* Here we define the states we will need to carry around in our Translation Functions *)

  (* In order to translate recursive functions we need the three following mappings:*)
  (* 1) Decreasing variables to function names *)
  Definition rec_args := alist Ced.Var string.

  (* 2) Function name to variable  *)
  Definition args_rec := alist string Ced.Var.

  (* 3) Function name to it's type signature *)
  Definition ftys := alist string Ced.Term.
  Definition rec_env := rec_args * args_rec * ftys.
  Definition fresh_renv: rec_env := (nil, nil, nil).

  Definition m A := readerT (global_env * ctx * rec_env) (eitherT string IdentityMonad.ident) A.
  Definition run_m {A} (env: global_env * ctx * rec_env) (ev: m A) := unIdent (unEitherT (runReaderT ev env)).
  Context {Monad_m : Monad m}.
  Context {Reader_m: MonadReader (global_env * ctx * rec_env) m}.
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
  '(genv, Γ, _) <- ask ;;
   match t with
   | tInd _ _ => ret true
   | tProd _ t1 t2 =>
     b1 <- isType t1 ;;
     b2 <- isType t2 ;;
     ret (andb b1 b2)
   | tConst kern _ =>
     cdecl <- option_m (lookup_constant kern genv) "Couldn't find cdecl body" ;;
     let cdecl_ty := (cst_type cdecl) in
     ret (isKind cdecl_ty)
   | tApp t _ => isType t
   | _ => ret false
   end.

  Fixpoint decl_exists (id : ident) (decls : global_env) : bool :=
  match decls with
  | [] => false
  | ConstantDecl kn d :: tl => (String.eqb (kername_to_qualid kn) id) || decl_exists id tl
  | InductiveDecl kn d :: tl =>
      if String.eqb (kername_to_qualid kn) id
      then true
      else
        let fix exists_constr (l : list ((ident × term) × nat)) :=
            match l with
            | nil => false
            | (c, _, _) :: tl => (String.eqb c id) || (exists_constr tl)
            end in
        let bdy := ind_bodies d in
        match head bdy with
        | None => decl_exists id tl
        | Some b => exists_constr (ind_ctors b) || decl_exists id tl
        end
  end.

  Fixpoint bound_var (x : ident) (Γ : ctx) : bool :=
  match Γ with
  | [] => false
  | x' :: xs => (String.eqb x x') || (bound_var x xs)
  end.

  Definition fresh (x: ident) : m ident :=
  '(genv, Γ, _) <- ask ;;
  if (bound_var x Γ) || (decl_exists x genv)
  (* TODO: Implement a smarter / nicer fresh generator *)
  then ret (append x "'")
  else ret x.

  Definition localDenote {A} (x: name) (r: m A): m (A * Ced.Name):=
  match x with
  | nAnon =>
    r' <- local (fun '(genv, Γ, renv) => (genv, "_" :: Γ, renv)) r ;;
    ret (r', Ced.Anon)
  | nNamed n =>
    x' <- fresh n ;;
    r' <- local (fun '(genv, Γ, renv) => (genv, x' :: Γ, renv)) r ;;
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
    '(genv, _, _) <- ask ;;
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

  Fixpoint countProds (t: term) : nat :=
  match t with
  | tProd _ _ bdy => S (countProds bdy)
  | _ => 0
  end.

  Definition get_rfunc_name (t: Ced.Term) (rarg: rec_args): option Ced.Var :=
  match t with
  | Ced.TVar x =>
    match (alist_find _ x rarg) with
    | Some fname => Some fname
    | None => None
    end
  | _ => None
  end.

  Fixpoint get_rargname (n: nat) (t: term): m ident :=
  match n with
  | O => match t with
        | tProd x _ _ => ret (get_ident x)
        | _ => raise "error fetching recursive argument name"
        end
  | S n' => match t with
           | tProd _ _ t' => get_rargname n' t'
           | _ => raise "error fetching recursive argument name"
           end
  end.

  Fixpoint get_nth_arg (n: nat) (t: term) : m (name * term * term) :=
  match n with
  | O => match t with
        | tProd x ty body => ret (x, ty, body)
        | _ => raise "term does not have requested arg argument"
        end
  | S n' => match t with
           | tProd x ty body =>
             '(x', ty', body') <- get_nth_arg n' body ;;
             ret (x', ty', (tProd x ty body'))
           | _ => raise "term does not have requested arg argument"
           end
  end.

  (* This function pull the nth argument of a lambda term
     and pulls it to be the first argument *)
  Definition normalize_type (t: term) (n: nat) : m term :=
  '(x', ty', t') <- get_nth_arg n t ;;
   ret (tProd x' ty' t').

  Reserved Notation "⟦ x ⟧" (at level 9).
  Fixpoint denoteKind (t: term): m Ced.Kind :=
  match t with
  | tSort _ => ret Ced.KdStar
  | tProd x t1 t2 =>
    k1 <- (if isKind t1
         then fmap inl (denoteKind t1)
         else fmap inr (denoteType t1)) ;;
    '(k2, x') <- localDenote x (denoteKind t2) ;;
    ret (Ced.KdAll x' k1 k2)
  | _ => raise "Ill-formed kind"
  end

  with denoteType (t: term): m Ced.Typ :=
  match t with
  | tRel n =>
    '(_, Γ, _) <- ask ;;
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
    ts' <- list_m (map (fun e => b <- isType e ;;
                             if b
                             then fmap inl (denoteType e)
                             else fmap inr (denoteTerm e))
                      ts) ;;
    ret (Ced.TyApp t' ts')
  | tLambda x kty t =>
    '(t', x') <- localDenote x (denoteType t) ;;
    if isKind kty
    then k <- denoteKind kty ;;
         ret (Ced.TyLamK x' k t')
    else ty <- denoteType kty ;;
         ret (Ced.TyLam x' ty t')
  | tInd ind univ => ret (Ced.TyVar (kername_to_qualid (inductive_mind ind)))
  | tFix _ _ => raise "type tFix not implemented yet"
  | tConstruct ind n _ => raise "type tConstruct not implemented yet"
  | tVar _ => raise "type tVar not implemented yet"
  | tEvar _ _ => raise "type tEvar not implemented yet"
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
  | tSort univ => ret (Ced.TVar "tSort")
  | tRel n =>
    '(_, Γ, _) <- ask ;;
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
  | tProd x kty t (*=> ret (Ced.TVar "tProd")*)
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
        ret (Ced.TDelta (eq_elim_term eq eqty x))
      | _ => ret (Ced.TVar "delwrong")
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
  | tProj _ _ => raise "tProj not implemented yet"
  | tCoFix _ _ => raise "tCoFix not implemented yet"
  | tConst kern _ => ret (Ced.TVar (kername_to_qualid kern))
  | tCast t _ _ => ⟦ t ⟧
  | tFix [f] _ =>
    let fname := getName (denoteName (dname f)) in
    let body := dbody f in
    let type := dtype f in
    let rec_arg := rarg f in
    '(genv, Γ, renv) <- ask ;;
    ty <- ⟦ type ⟧ ;;
    rargname <- get_rargname rec_arg type ;;
    (* rargname <- option_m (nth_error Γ' rec_arg) ("ty tRel " ++ utils.string_of_nat rec_arg ++ " not in environment " ++ showList Γ);; *)
    (* Definition rec_args := alist Ced.Var string. *)
    (* Definition args_rec := alist string Ced.Var. *)
    (* Definition ftys := alist string term. *)
    (* Definition rec_env := rec_args * args_rec * ftys. *)
    let '(rarg, argr, fts) := renv in
    let renv' := (alist_add _ rargname fname rarg,
                  alist_add _ fname rargname argr,
                  alist_add _ fname ty fts) in
    local (fun '(_, _, _) => (genv, fname :: Γ, renv')) ⟦ body ⟧

  | tFix _ _ => raise "Ill formed fixpoint"
  | tCase (ind, npars) mot c brchs =>
    '(_, _, renv) <- ask ;;
    let '(rarg, _, _) := renv in
    ctors <- get_ctors ind ;;
    c' <- ⟦ c ⟧ ;;
    mot' <- denoteType mot ;;
    args <- list_m (map take_args brchs) ;;
    brchs' <- list_m (map (fun '(_, t) => (local (fun '(genv, Γ, renv) => (genv, Γ, renv)) (denoteTerm t))) brchs) ;;
    let trimmed_brchs' := map (fun '(n, t) => removeLambdas n t) (combine (map fst brchs) brchs') in
    let constrs := map build_tApp (combine ctors args) in
    let fname := get_rfunc_name c' rarg in
    ret (Ced.TMu fname c' (Some mot') (combine constrs trimmed_brchs'))
  end
  where "⟦ x ⟧" := (denoteTerm x).

  Fixpoint denoteCtors (data_name : Ced.Var)
           (params: Ced.Params)
           (ctor: (ident * term) * nat) : m Ced.Ctor  :=
  let '(name, t, i) := ctor in
  let paramnames := map fst params in
  t' <- local (fun '(genv, _, _) => (genv, [data_name], fresh_renv)) (denoteType t) ;;
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
  if String.eqb name "False"
  then ret (Ced.CmdAssgn False_term)
  else
    let ctors := ind_ctors body in
    let param_l := rev (ind_params mbody) in
    let param_names := map (get_ident ̊ decl_name) param_l in
    params <- denoteParams param_l;;
    let tki := ind_type body in
    ki <- local (fun '(genv, _, _) => (genv, nil, fresh_renv)) (denoteKind tki) ;;
    ctors' <- list_m (map (denoteCtors name (rev params)) ctors);;
    ret (Ced.CmdData (Ced.DefData name params ki ctors')).

  Fixpoint denoteGenv (genv: global_env): m Ced.Program :=
  match genv with
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
  Definition denoteCoq' (t: term): m Ced.Program :=
  (* TODO: Update this for denoteGenv only use the genvs seen so far *)
  '(genv, _, _) <- ask;;
   denoteGenv genv.

End monadic.

Instance m_Monad : Monad m.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadReader : MonadReader (global_env * ctx * rec_env) m.
apply MonadReader_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadExc : MonadExc string m.
apply MonadExc_readerT.
apply Exception_eitherT.
apply Monad_ident.
Defined.

Definition denoteCoq (p: program): string + Ced.Program :=
let '(genv, t) := p in
run_m (genv, nil, fresh_renv) (denoteCoq' t).
