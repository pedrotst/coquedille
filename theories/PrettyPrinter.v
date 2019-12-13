Require Import Coquedille.Ast.
Import Ced.

Require Import List.
Require Import String.
Local Open Scope string.

Require Import Coquedille.DenoteCoq.
(* Require Import Coquedille.Utils. *)

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Map.FMapAList.
Import MonadNotation.

(* Token Definitions *)
Definition TkNotImpl   := "ppNotImpl".
Definition TkStar      := "★".
Definition TkArrow     := "➔".
Definition TkSpace     := " ".
Definition TkColon     := ":".
Definition TkPipe      := "|".
Definition TkDot       := ".".
Definition TkTab       := "  ".
Definition TkAnon      := "anon".
Definition TkPi        := "Π".
Definition TkAll       := "∀".
Definition TkOpenPar   := "(".
Definition TkClosePar  := ")".
Definition TkTpDot     := "·".
Definition TkData      := "data".
Definition TkAssgn     := "=".
Definition TkCR        := "
".

Class Pretty (p : Type) :=
  pretty : p -> string.


Definition type_ctx := alist Ced.Var Ced.Typ.

Fixpoint ppIndentation (n : nat) :=
  match n with
  | O => ""
  | S n => TkTab ++ ppIndentation n
  end.

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) (indentation: nat): string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => ppIndentation indentation ++ f a
      | cons a l => ppIndentation indentation ++ f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) (indentation: nat): string :=
  string_of_list_aux f TkCR l indentation.

Instance PrettyName : Pretty Name :=
  fun name =>
    match name with
    | Anon => TkAnon
    | Named v => v
    end.

Definition parens (b: bool) (s : string) :=
  if b then TkOpenPar ++ s ++ TkClosePar else s.

Local Open Scope monad_scope.
Definition string_eq x y := utils.string_compare x y = Eq.

Instance string_RelDec : RelDec.RelDec string_eq :=
  { rel_dec := eqb }.

Definition ppDot (t: Typ) : state type_ctx string :=
  Γ <- get ;;
  match t with
  | TpVar v =>
    match alist_find _ v Γ with
    | None => ret "1"
    | Some t =>
      match t with
      | KdStar => ret TkTpDot
      | _ => ret "2"
      end
    end
  | _ => ret "3"
  end.

Fixpoint ppTerm' (barr bapp: bool) (t : Typ): state type_ctx string :=
  match t with
  | TpPi x t1 t2 =>
    match x with
    | Anon =>
      Γ <- get ;;
      t1' <- ppTerm' true false t1 ;;
      put Γ ;;
      t2' <- ppTerm' false false t2 ;;
      ret (parens barr (t1' ++ TkSpace ++ TkArrow ++ TkSpace ++ t2'))
    | Named name =>
      Γ <- get ;;
      t1' <- ppTerm' false false t1 ;;
      put ((name, t1) :: Γ) ;;
      t2' <- ppTerm' false false t2 ;;
      ret (TkPi ++ TkSpace ++ name ++ TkSpace
                ++ TkColon ++ TkSpace
                ++ t1' ++ TkSpace
                ++ TkDot ++ TkSpace ++ t2')
    end
  | TpApp t1 ts2 =>
    Γ <- get ;;
    t1' <- ppTerm' false false t1 ;;
    let ppApp (t: Typ) : state type_ctx string :=
        d <- ppDot t ;;
        t' <- ppTerm' false true t ;;
        ret (d ++ t') in
    put Γ ;;
    ts2' <- list_m (map ppApp ts2) ;;
    ret (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
  | TpVar v => ret v
  | KdStar => ret TkStar
  end.

Definition ppTerm (t: Typ) (Γ : type_ctx) :=
  fst (@runState _ _ (ppTerm' false false t) Γ).

Fixpoint removeBindings' (t: Typ) (n: nat) : state type_ctx Typ :=
match n with
| O => ret t
| S n' =>
  match t with
  | TpPi x t1 t2 =>
    Γ <- get ;;
    t' <- removeBindings' t2 (pred n);;
    match x with
    | Anon => ret t'
    | Named name =>
      put ((name, t1) :: Γ) ;;
      ret t'
    end
  | _ => ret t
  end
end.

Fixpoint removeN {A} (l: list A) (n: nat): list A :=
  match n with
  | O => l
  | S n' =>
    match l with
    | cons _ xs => removeN xs n'
    | nil => nil
    end
  end.

Definition flattenApp (t: Typ) :=
  match t with
  | TpApp t nil => t
  | _ => t
  end.

Fixpoint removeParams (data_name : Var) params_count (t: Typ) :=
  let removeParams' := removeParams data_name params_count in
  match t with
  | TpApp t1 ts2 =>
    let rs := map removeParams' ts2 in
    match t1 with
    | TpVar v =>
      if (string_dec v data_name)
      then let rs' := removeN rs params_count in
           flattenApp (TpApp t1 rs')
      else flattenApp (TpApp t1 rs)
    | _ => TpApp (removeParams' t1) ts2
    end
  | TpPi x t1 t2 => TpPi x (removeParams' t1) (removeParams' t2)
  | _ => t
  end.

Definition removeBindings ty params_count :=
  @runState _ _ (removeBindings' ty params_count) nil.

Definition ppctor params_count (Γ: type_ctx) data_name ctor :=
  match ctor with
  | Ctr cname ty =>
    let '(no_bindings_t, Γ') := removeBindings ty params_count in
    let no_params_t := removeParams data_name params_count no_bindings_t in
    TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ ppTerm no_params_t (List.app Γ Γ')
  end.

Instance PrettyParams : Pretty Params :=
  fix pp params :=
    match params with
    | nil => ""
    | cons (n, t) ps =>
      TkSpace ++ TkOpenPar ++ n ++ TkSpace
              ++ TkColon ++ TkSpace ++ (ppTerm t nil)
              ++ TkClosePar ++ pp ps
    end.

Definition alist_app (a1 a2: alist Var Typ) : alist Var Typ :=
  @fold_alist _ _ _ (@alist_add _ _ _ _) a1 a2.

Definition ppDatatype (name : Var) (params: Params) (kind : Typ) (ctors : list Ctor) : state type_ctx string :=
  Γ <- get ;;
  k <- removeBindings' kind (List.length params) ;;
  (* put (alist_app params Γ) ;; *)
  ty <- ppTerm' false false k ;;
  let ctors' := string_of_list (ppctor (List.length params) Γ name) ctors 1 in
  ret (TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ ty ++ TkSpace ++ TkAssgn ++ TkCR
          ++ ctors' ++ TkDot).

Definition ppType (ty : option Typ) :=
  match ty with
  | None => ""
  | Some t => TkColon ++ TkSpace ++ ppTerm t nil ++ TkSpace
  end.


Instance PrettyAssgn : Pretty Assgn :=
  fun asgn =>
    match asgn with
    | AssgnType name ty t => name ++ TkSpace ++ ppType ty ++ TkAssgn
                              ++ TkSpace ++ ppTerm t nil
                              ++ TkDot ++ TkCR
    (* | AssgnTerm name t => TkNotImpl *)
    end.

Definition ppCmd (c: Cmd): state type_ctx string :=
  Γ <- get ;;
  match c with
  | CmdAssgn (AssgnType v mty t) =>
    match mty with
    | None => ret (pretty (AssgnType v mty t))
    | Some ty => put (alist_add _ v ty Γ);;
                ret (pretty (AssgnType v mty t))
    end
  | CmdData (DefData name params kind ctors)  =>
    put (alist_add _ name kind Γ) ;;
    s <- ppDatatype name params kind ctors ;;
    ret (s ++ TkCR)
  end.

Fixpoint ppProgram' (p : Program) : state type_ctx string :=
  match p with
  | nil => ret ""
  | c :: cs =>
    c' <- ppCmd c;;
    cs' <- ppProgram' cs;;
    ret (c' ++ TkCR ++ cs')
  end.

Instance PrettyProgram : Pretty Program :=
  fun p => fst (@runState _ _ (ppProgram' p) nil).

Definition showState :=
  fun p => snd (@runState _ _ (ppProgram' p) nil).

Instance PrettyOption {A} {x: Pretty A}: Pretty (option A) :=
  fun o =>
    match o with
      (* Maybe signal an error? *)
    | None => ""
    | Some x => pretty x
    end.

Instance PrettySum {A} {x: Pretty A}: Pretty (string + A) :=
  fun y =>
    match y with
    | inl s =>  s
    | inr a => pretty a
    end.

Local Close Scope string_scope.
Local Close Scope monad_scope.
