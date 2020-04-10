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

Require Import ExtLib.Core.RelDec.

Require Import Coq.Sorting.Mergesort.
Module Import NatSort := Sort NatOrder.

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
  (* 1) Recursive variables to function names *)
  Definition a_rargs := alist Ced.Var string.

  (* 2) Function Name to its decreasing variable number *)
  (* this is used to reorganize the tApp structure *)
  (* TODO: make this a list of nat with all the parameters *)
  Definition a_rargspos := alist Ced.Var nat.

  (* 3) The remaining non-recursive arguments of the function to bind at each branch *)
  Definition a_nrargs := alist Ced.Var (list (Ced.Var * Ced.Sort)).

  (* 4) Function name to it's type signature *)
  Definition a_motives := alist Ced.Var Ced.Typ.

  (* 5) Function name to reorg list used to reorganize the applications *)
  Definition a_reorg := alist Ced.Var (list nat).

  Definition rec_env := a_rargs * a_rargspos * a_nrargs * a_motives * a_reorg.

  Definition params_env := alist Ced.Var nat.

  Definition fresh_renv: rec_env := (nil, nil, nil, nil, nil).

  Definition m A := stateT params_env
                           (readerT (global_env * ctx * rec_env)
                                    (eitherT string IdentityMonad.ident)) A.

  Definition run_m {A} (params: params_env) (env: global_env * ctx * rec_env) (ev: m A) := unIdent (unEitherT (runReaderT (runStateT ev params) env)).
  Context {Monad_m : Monad m}.
  Context {Reader_m: MonadReader (global_env * ctx * rec_env) m}.
  Context {State_m: MonadState params_env m}.
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

  Definition get_ctors ind : m (list ctor_typ) :=
    '(genv, _, _) <- ask ;;
    let minds := inductive_mind ind in
    m_decl <- option_m (lookup_mind_decl minds genv) "Declaration not found" ;;
    let bodies := ind_bodies m_decl in
    body <- option_m (head bodies) "Could not find declaration body" ;;
    ret (ind_ctors body).

  Definition build_tApp (nts: ctor_typ * list (Ced.Typ + Ced.Term)) :=
  let '(ctor, ts) := nts in
  let '(n, _, _) := ctor in
  Ced.TApp (Ced.TVar n) (map (fun t => (false, t)) ts).

  Definition get_ctor_name : ctor_typ -> ident :=
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

  Definition get_rfunc_name (t: Ced.Term) (rarg: a_rargs): option Ced.Var :=
  match t with
  | Ced.TVar x =>
    match (alist_find _ x rarg) with
    | Some fname => Some fname
    | None => None
    end
  | _ => None
  end.

  Fixpoint get_fvariables (t: Ced.Typ): list (Ced.Var * Ced.Typ):=
  match t with
  | Ced.TyPi x ty t' => ((getName x), ty) :: get_fvariables t'
  | _ => nil
  end.

  Definition get_motive (x: option ident) (mfty: a_motives) (default: Ced.Typ) :=
  match x with
  | None => default
  | Some x' => match alist_find _ x' mfty with
              | None => default
              | Some mot => mot
              end
  end.

  Fixpoint pull_nth_arg (n: nat) (t: Ced.Typ) : m (Ced.Name * Ced.Typ * Ced.Typ) :=
  match n with
  | O => match t with
        | Ced.TyPi x ty body => ret (x, ty, body)
        | _ => raise "term does not have requested arg argument"
        end
  | S n' => match t with
           | Ced.TyPi x ty body =>
             '(x', ty', body') <- pull_nth_arg n' body ;;
             ret (x', ty', (Ced.TyPi x ty body'))
           | _ => raise "term does not have requested arg argument"
           end
  end.

  Fixpoint eraseNones {A} (ls: list (option A)): list A :=
  match ls with
  | (Some x) :: l => x :: eraseNones l
  | None :: l => eraseNones l
  | nil => nil
  end.

  Fixpoint delete_nth {A} (l: list A) (n:nat): list A :=
  match l with
  | nil => nil
  | x :: xs => match n with
             | O => xs
             | S n' => x :: delete_nth xs n'
             end
  end.

  Fixpoint nth_to_head {A} (l: list A) (n: nat) : list A :=
  match nth_error l n with
  | None => l
  | Some x => x :: delete_nth l n
  end.

  Definition nth_many {A} (l: list A) (r: list nat): list A :=
  eraseNones (map (nth_error l) r).

  Definition delete_many {A} (l: list A) (dels: list nat) :=
  fold_right (fun a l' => delete_nth l' a) l dels.

  Fixpoint tag_last {A} (l: list A) {struct l} : list (bool * A) :=
  match l with
  | nil => nil
  | [a] => [(false, a)]
  | a1 :: (_ :: _) as l0 => (true, a1) :: tag_last l0
  end.

  (* FIXME: Notice that if the function name is hidden behind another definition this will not work because
     it expects that it is a TVar directly. Solving this seems tricky *)
  Definition reorg_app_args {A} (t: Ced.Term) (l: list A) : m (list (bool * A)) :=
  let tag := map (fun x => (false, x)) in
  match t with
  | Ced.TVar x =>
    '(_, _, renv) <- ask ;;
     let '(_, _, _, _, reorg) := renv in
     match alist_find _ x reorg with
     | Some re =>
       let items := tag_last (nth_many l re) in
       let sorted_re := (sort re) in
       let tail := delete_many l sorted_re in
       ret (items ++ tag tail)
     | None => ret (tag l)
     end
  | _ => ret (tag l)
  end.

  Fixpoint tyAppVars' (ts: list Ced.TyTerm) :=
  let peel t :=
      match t with
      | inl (Ced.TyVar x) => Some x
      | inr (Ced.TVar x) => Some x
      | _ => None
      end
  in match ts with
     | t :: ts => peel t :: tyAppVars' ts
     | nil => nil
     end.

  Definition tyAppVars := eraseNones ̊ tyAppVars'.

  Definition app_inl {A B C} (f: A -> C) (x: A + B) : option C :=
  match x with
  | inl a => Some (f a)
  | inr _ => None
  end.

  (* There may be some monadic functions to take care of these auxiliar
  functions for us *)
  Definition map_inl {A B X C} (f: A -> C)  (l: list (X * (A + B))): list C
    := eraseNones (map (fun '(_, ab) => app_inl f ab) l).

  Definition map_pair {A B} (f: A -> B) A * A -> B * B :=
  fun '(a1, a2) => (f a1, f a2).

  Fixpoint delparamsTy (penv: params_env) (ty: Ced.Typ) {struct ty}: Ced.Typ :=
  let dparTy := delparamsTy penv in
  let dparT := delparamsT penv in
  let dparK := delparamsK penv in
  let c (bkt: bool * Ced.TyTerm) :=
      let '(b, kt) := bkt in
      match kt with
      | inl ty => (b, inl (dparTy ty))
      | inr t => (b, inr (dparT t))
      end in
  match ty with
  | Ced.TyIntersec x ty' b => Ced.TyIntersec x (dparTy ty') (dparTy b)
  | Ced.TyPi x ty' b => Ced.TyPi x (dparTy ty') (dparTy b)
  | Ced.TyLam x ty' b => Ced.TyLam x (dparTy ty') (dparTy b) (**)
  | Ced.TyAll x k b => Ced.TyAll x (dparK k) (dparTy b)
  | Ced.TyAllT x ty b => Ced.TyAllT x (dparTy ty) (dparTy b)
  | Ced.TyLamK x k b => Ced.TyLamK x (dparK k) (dparTy b)
  | Ced.TyApp (Ced.TyVar x) apps =>
    match alist_find _ x penv with
    | Some n => Ced.TyApp (Ced.TyVar x) (skipn n apps)
    | None => Ced.TyApp (Ced.TyVar x) (map c apps)
    end
  | Ced.TyApp t' apps =>
    Ced.TyApp t' (map c apps)
  | Ced.TyVar _ => ty
  | Ced.TyEq  t1 t2 => Ced.TyEq (delparamsT penv t1) (delparamsT penv t1)
  end
  with delparamsK (penv: params_env) (k: Ced.Kind) {struct k}: Ced.Kind :=
  match k with
  | Ced.KdStar => Ced.KdStar
  | Ced.KdAll x kty k' =>
    let kty' := match kty with
                | inl ki => inl ki
                | inr ty => inr (delparamsTy penv ty)
                end in
    Ced.KdAll x kty' (delparamsK penv k')
  end
  with delparamsT (penv: params_env) (t: Ced.Term) {struct t}: Ced.Term :=
  let dparTy := delparamsTy penv in
  let dparT := delparamsT penv in
  let dparK := delparamsK penv in
  let c (bkt: bool * Ced.TyTerm) :=
      let '(b, kt) := bkt in
      match kt with
      | inl ty => (b, inl (dparTy ty))
      | inr t => (b, inr (dparT t))
      end in
  match t with
  | Ced.TVar x => t
  | Ced.TLam x er ty b => Ced.TLam x er (dparTy ty) (dparT b)
  | Ced.TLamK x k b => Ced.TLamK x (dparK k) (dparT b)
  | Ced.TApp t apps => Ced.TApp (dparT t) (map c apps)
  | Ced.TLetTm x er ty t' b => Ced.TLetTm x er (dparTy ty) (dparT t') (dparT b)
  | Ced.TLetTy x k ty b => Ced.TLetTy x k (dparTy ty) (dparT b)
  | Ced.TDelta b => Ced.TDelta (dparT b)
  | Ced.TRho t1 t2 => Ced.TRho (dparT t1) (dparT t2)
  | Ced.TBeta => Ced.TBeta
  | Ced.TMu x t' mot bs => Ced.TMu x (dparT t') (option_map dparTy mot)
                          (map (map_pair dparT) bs)
  end.

  Definition deleteparams (penv: params_env) (kty: Ced.Sort) : Ced.Sort:=
  match kty with
  | inr ty => inr (delparamsTy penv ty)
  | inl k => inl (delparamsK penv k)
  end.

  (* FIXME: I think we need to define this for terms and types too *)
  Fixpoint get_depsTy (ty: Ced.Typ) : list Ced.Var :=
  match ty with
    | Ced.TyIntersec _ t1 t2
    | Ced.TyPi _ t1 t2
    | Ced.TyLam _ t1 t2 => get_depsTy t1 ++ get_depsTy t2
    | Ced.TyAll _ _ t'
    | Ced.TyAllT _ _ t'
    | Ced.TyLamK _ _ t' => get_depsTy t'
    | Ced.TyApp t' apps =>
      get_depsTy t' ++ concat (map_inl get_depsTy apps) ++ tyAppVars (map snd apps)
    | Ced.TyVar x => [x]
    | Ced.TyEq _ _ => nil  end.

  Definition get_deps (penv: params_env) (kty: Ced.Sort): list Ced.Var :=
  match kty with
  | inr ty => get_depsTy (delparamsTy penv ty)
  | _ => nil
  end.

  Definition mot_env := alist Ced.Var Ced.Sort.

  Fixpoint build_env' (ty: Ced.Typ) (acc: mot_env): mot_env :=
  match ty with
  | Ced.TyAll n k b => build_env' b (alist_add _ (getName n) (inl k) acc)
  | Ced.TyPi n ty b => build_env' b (alist_add _ (getName n) (inr ty) acc)
  | _ => acc
  end.

  Fixpoint get_body (t: Ced.Typ): Ced.Typ :=
  match t with
  | Ced.TyAll _ _ b => get_body b
  | Ced.TyPi _ _ b => get_body b
  | _ => t
  end.

  Definition build_env t := rev (build_env' t nil).

  Fixpoint pull_env (env: mot_env) (x: Ced.Var) (bdy: Ced.Typ) : Ced.Typ * mot_env :=
  match alist_find _ x env with
  | Some ty =>
    let t' := match ty with
              | inl xk => Ced.TyAll (Ced.Named x) xk bdy
              | inr xty => Ced.TyPi (Ced.Named x) xty bdy
              end in
      (t', (alist_remove _ x env))
  | None => (bdy, env)
  end.

  (* Inserts Pi x ty in the end of the lambda list *)
  Fixpoint insert_pi_body (t: Ced.Typ) (x: Ced.Var) (kty: Ced.Kind + Ced.Typ): Ced.Typ :=
  match t with
  | Ced.TyLam x' ty' b => Ced.TyLam x' ty' (insert_pi_body b x kty)
  | _ => match kty with
        | inr ty => Ced.TyPi (Ced.Named x) ty t
        | inl k => Ced.TyAll (Ced.Named x) k t
        end
  end.

  (* Inserts Lam x ty in the begining of the lambda list *)
  Fixpoint insert_lam_body (t: Ced.Typ) (x: Ced.Var) (kty: Ced.Kind + Ced.Typ): Ced.Typ :=
  match kty with
  | inl k => Ced.TyLamK (Ced.Named x) k t
  | inr ty => Ced.TyLam (Ced.Named x) ty t
  end.

  Definition unfold_env (t: Ced.Typ) (env: mot_env)
    := fold_right (fun '(x, ty) t' => insert_pi_body t' x ty) t env.

  Definition alist_remove_many (l: list Ced.Var) (env: mot_env) :=
  fold_right (fun x env' => alist_remove _  x env') env l .

  Fixpoint alist_find_many (l: list Ced.Var) (env: mot_env) :=
  match l with
  | nil => nil
  | x :: xs => alist_find _ x env :: alist_find_many xs env
  end.

  (* The function zips two lists by pulling out the elements of the option functor in the second list *)
  (* If the second element is a None, then it ignores not only that element, but
  also the matching element in the first list *)
  Fixpoint combine_maybe {A B} (xs: list A) (ys: list (option B)): list (A * B) :=
  match xs, ys with
  | x :: xs, (Some y) :: ys => (x, y) :: combine_maybe xs ys
  | x :: xs, None :: ys => combine_maybe xs ys
  | _, _ => nil
  end.

  Definition build_lam (t: Ced.Typ) (env: mot_env) :=
  fold_right (fun '(x, ty) t' => insert_lam_body t' x ty) t env.

  Fixpoint alist_pos' {K V R} `{RelDec _ R} (acc: nat) (m: alist K V) (k: K): option nat :=
  match m with
  | nil => None
  | (k', _) :: ms => if (k ?[ R ] k')
                   then Some acc
                   else alist_pos' (S acc) ms k
  end.
  Definition alist_pos {K V R RD_K} := @alist_pos' K V R RD_K 0.

  Program Fixpoint pull_deps t deps fvars penv { measure #|fvars| } :=
  let fvars' := alist_remove_many deps fvars in
  let deps_ty := alist_find_many deps fvars in
  let ts := combine_maybe deps deps_ty in
  let t' := build_lam t ts in
  let tys := map snd ts in
  (* let erased_tys := map (deleteparams penv) tys in *)
  let deps' := concat (map (get_deps penv) tys) in
  if eq_nat #|deps'| 0
  then (t', fvars')
  else pull_deps t' deps' fvars' penv.
  Next Obligation.
    admit.
  Admitted.

  Fixpoint get_lambodies (t: Ced.Typ) : list Ced.Var :=
  match t with
  | Ced.TyLam x _ b
  | Ced.TyLamK x _ b => (getName x) :: get_lambodies b
  | _ => nil
  end.

  (* This function pull the nth argument of a lambda term
     and pulls it to be the first argument *)
  (* TODO: Recursivelly pull dependent variables *)
  Definition denoteMotive (mot: Ced.Typ) (rargpos: nat) fname : m rec_env:=
  let body := get_body mot in
  let fvars := build_env mot in
  penv <- get ;;
  '(rarg, rarg_ty) <- option_m (nth_error fvars rargpos) ("error fetching recursive argument name for motive in " ++ showList (map fst fvars)) ;;
  let nargs := alist_remove _ rarg fvars in
  let deps := get_deps penv rarg_ty in
  let t' := insert_lam_body body rarg rarg_ty in
  let '(t'', nargs') := pull_deps t' deps nargs penv in
  let boundvars := get_lambodies t'' in
  let reorgs := map (alist_pos fvars) boundvars in
  let mot' := unfold_env t'' nargs' in
  '(_, _, (arargs, arpos, anargs, amots, reorg)) <- ask ;;
  let renv' := (alist_add _ rarg fname arargs,
                 alist_add _ fname rargpos arpos,
                 alist_add _ fname nargs' anargs,
                 alist_add _ fname mot' amots,
                 alist_add _ fname (eraseNones reorgs) reorg) in
  ret renv'.

  Definition flattenTApp (t: Ced.Term) :=
  match t with
  | Ced.TApp t' nil => t'
  | _ => t
  end.

  Definition get_nrargs (fname: option Ced.Var) (nrargs: a_nrargs) :=
  match fname with
  | None => nil
  | Some x => match alist_find _ x nrargs with
             | None => nil
             | Some l => l
             end
  end.

  Fixpoint bind_nrargs (nrargs: list (Ced.Var * Ced.Sort)) (tail: Ced.Term) :=
  let fresh x := append x "'" in
  match nrargs with
  | nil => tail
  | (x, inr ty) :: ts => Ced.TLam (Ced.Named (fresh x)) false ty (bind_nrargs ts tail)
  | (x, inl k) :: ts => Ced.TLamK (Ced.Named (fresh x)) k (bind_nrargs ts tail)
  end.

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
                             then fmap (fun x => (false, inl x)) (denoteType e)
                             else fmap (fun x => (false, inr x)) (denoteTerm e))
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

    ts'' <- reorg_app_args t' ts';;
    ret (Ced.TApp t' ts'')
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
      | Ced.TApp _ ([(false, inl eqty); (false, inr x); _; _; (false, inr y); (false, inr eq)]) =>
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
    let fname := get_ident (dname f) in
    let body := dbody f in
    let type := dtype f in
    let rarg_pos := rarg f in
    ty <- denoteType type ;;
    renv' <- denoteMotive ty rarg_pos fname;;
    local (fun '(genv, Γ, renv) => (genv, fname :: Γ, renv')) ⟦ body ⟧
  | tFix _ _ => raise "Mutually recursive fixpoints not implemented yet"
  | tCase (ind, npars) mot matchvar brchs =>
    '(_, _, renv) <- ask ;;
    let '(arargs, _, anargs, amots, _) := renv in
    ctors <- get_ctors ind ;;
    matchvar' <- ⟦ matchvar ⟧ ;;
    mot' <- denoteType mot ;;
    args <- list_m (map take_args brchs) ;;
    brchs_t' <- list_m (map (fun '(_, t) => ⟦ t ⟧) brchs) ;;
    let brchs_n := map fst brchs in
    let trimmed_brchs' := map (fun '(n, t) => removeLambdas n t) (combine brchs_n brchs_t') in
    let constrs := map build_tApp (combine ctors args) in
    let flat_constrs := map flattenTApp constrs in
    let fname := get_rfunc_name matchvar' arargs in
    let mot' := get_motive fname amots mot' in
    let app_args := get_nrargs fname anargs in
    (* TODO: instead of removing and rebinding we can just remove the necessary ones
       this may actually make anargs unecessary *)
    let nrargs_brchs := map (bind_nrargs app_args) trimmed_brchs' in
    (* FIXME: actually figure out if the argument is a type or a term, for now we assume its a term *)
    let tapp_args := map (fun x => (false, (inr ̊ Ced.TVar ̊ fst) x)) app_args in
    let t' := Ced.TApp (Ced.TMu fname matchvar' (Some mot') (combine flat_constrs nrargs_brchs)) tapp_args in
    ret (flattenTApp t')
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
  | p :: ps =>
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
    penv <- get ;;
    put (alist_add _ name (length params) penv) ;;
    ctors' <- list_m (map (denoteCtors name (rev params)) ctors);;
    ret (Ced.CmdData (Ced.DefData name params ki ctors')).

  Fixpoint denoteGenv (genv: global_env): m Ced.Program :=
  match genv with
  | nil => ret nil
  | e :: es' =>
    match e with
    | InductiveDecl kern mbody =>
      p <- denoteInductive mbody ;;
      ps <- denoteGenv es';;
      ret (p :: ps)
    | ConstantDecl kern cbody =>
      ps <- denoteGenv es';;
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
apply Monad_stateT.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadReader : MonadReader (global_env * ctx * rec_env) m.
apply MonadReader_stateT.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
apply MonadReader_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadExc : MonadExc string m.
apply Exc_stateT.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
apply MonadExc_readerT.
apply Exception_eitherT.
apply Monad_ident.
Defined.

Instance m_MonadState : MonadState params_env m.
apply MonadState_stateT.
apply Monad_readerT.
apply Monad_eitherT.
apply Monad_ident.
Defined.

Definition denoteCoq (p: program): string + Ced.Program :=
let '(genv, t) := p in
match run_m nil (genv, nil, fresh_renv) (denoteCoq' t) with
| inl l => inl l
| inr (p, _) => inr p
end.
