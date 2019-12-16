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
Require Import ExtLib.Data.Monads.WriterMonad.
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
Definition TkTDot      := "·".
Definition TkData      := "data".
Definition TkLam       := "λ".
Definition TkAssgn     := "=".
Definition TkCR        := "
".

Class Pretty (p : Type) :=
  pretty : p -> string.

Local Open Scope monad_scope.
Definition type_ctx := alist Ced.Var Ced.Term.

Definition string_eq x y := utils.string_compare x y = Eq.

Instance string_RelDec : RelDec.RelDec string_eq :=
  { rel_dec := eqb }.

Definition alist_app (a1 a2: alist Var Term) : alist Var Term :=
  @fold_alist _ _ _ (@alist_add _ _ _ _) a1 a2.

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

Definition ppDot (t: Term) : reader type_ctx string :=
  Γ <- ask ;;
  match t with
  | TVar v =>
    match alist_find _ v Γ with
    | None => ret ""
    | Some t =>
      match t with
      | KdStar => ret TkTDot
      | _ => ret ""
      end
    end
  | _ => ret ""
  end.

Fixpoint ppTerm' (barr bapp: bool) (t : Term): reader type_ctx string :=
  match t with
  | TPi x t1 t2 =>
    match x with
    | Anon =>
      t1' <- ppTerm' true false t1 ;;
      t2' <- ppTerm' false false t2 ;;
      ret (parens barr (t1' ++ TkSpace ++ TkArrow ++ TkSpace ++ t2'))
    | Named name =>
      t1' <- ppTerm' false false t1 ;;
      t2' <- local (fun Γ => ((name, t1) :: Γ)) (ppTerm' false false t2) ;;
      ret (TkPi ++ TkSpace ++ name ++ TkSpace
                ++ TkColon ++ TkSpace
                ++ t1' ++ TkSpace
                ++ TkDot ++ TkSpace ++ t2')
    end
  | TApp t1 ts2 =>
    t1' <- ppTerm' false true t1 ;;
    let ppApp (t: Term) : reader type_ctx string :=
        d <- ppDot t ;;
        t' <- ppTerm' false true t ;;
        ret (d ++ t') in
    ts2' <- list_m (map ppApp ts2) ;;
    ret (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
  | TLam x ty t =>
    ty' <- ppTerm' false false ty ;;
    t' <- ppTerm' false false t;;
    let x' := match x with | Anon => "_" | Named y => y end in
    ret (parens bapp (TkLam ++ TkSpace ++ x' ++ TkSpace
                            ++ TkColon ++ TkSpace ++ ty' ++ TkSpace
                            ++ TkDot ++ TkSpace ++ t'))
  | TVar v => ret v
  | KdStar => ret TkStar
  end.

Definition ppTerm (t: Term) (Γ : type_ctx) :=
  (@runReader _ _ (ppTerm' false false t) Γ).

Fixpoint removeBindings (t: Term) (n: nat) : state type_ctx Term :=
match n with
| O => ret t
| S n' =>
  match t with
  | TPi x t1 t2 =>
    Γ <- get ;;
    t' <- removeBindings t2 (pred n);;
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

Definition flattenApp (t: Term) :=
  match t with
  | TApp t nil => t
  | _ => t
  end.

Fixpoint removeParams (data_name : Var) params_count (t: Term) :=
  let removeParams' := removeParams data_name params_count in
  match t with
  | TApp t1 ts2 =>
    let rs := map removeParams' ts2 in
    match t1 with
    | TVar v =>
      if (string_dec v data_name)
      then let rs' := removeN rs params_count in
           flattenApp (TApp t1 rs')
      else flattenApp (TApp t1 rs)
    | _ => TApp (removeParams' t1) ts2
    end
  | TPi x t1 t2 => TPi x (removeParams' t1) (removeParams' t2)
  | _ => t
  end.

Definition ppctor params_count data_name ctor: reader type_ctx string :=
  match ctor with
  | Ctr cname ty =>
    Γ <- ask ;;
    let '(no_bindings_t, Γ') := runState (removeBindings ty params_count) Γ in
    (* Apps with the constructor in cedille doesn't explicitely show the parameters *)
    let no_params_t := removeParams data_name params_count no_bindings_t in
    t' <- local (fun _ => (alist_app Γ Γ')) (ppTerm' false false no_params_t) ;;
    ret (TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ t')
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

Program Definition ppDatatype (name : Var) (params: Params) (kind : Term) (ctors : list Ctor) : reader type_ctx string :=
  Γ <- ask ;;
  let '(k, _) := runState (removeBindings kind (List.length params)) nil in
  ty <- ppTerm' false false k ;;
  (* Working on the reader monad here makes the mapping trivial *)
  ctorlist <- list_m (map (ppctor (List.length params) name) ctors) ;;
  let ctors' := string_of_list id ctorlist 1 in
  ret (TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ ty ++ TkSpace ++ TkAssgn ++ TkCR
          ++ ctors' ++ TkDot).

Definition ppmType (v: Var) (mty : option Term) : state type_ctx string :=
  match mty with
  | None => ret ""
  | Some ty =>
    Γ <- get ;;
    put (alist_add _ v ty Γ);;
    ret (TkColon ++ TkSpace ++ ppTerm ty Γ ++ TkSpace)
  end.

Instance PrettyOption {A} {x: Pretty A}: Pretty (option A) :=
  fun o =>
    match o with
    | None => "ERR"
    | Some x => pretty x
    end.

Instance PrettySum {A} {x: Pretty A}: Pretty (string + A) :=
  fun y =>
    match y with
    | inl s =>  s
    | inr a => pretty a
    end.

Program Definition ppCmd (c: Cmd): state type_ctx string :=
  Γ <- get ;;
  match c with
  | CmdAssgn (AssgnType v mty t) =>
    typ <- ppmType v mty ;;
    ret (v ++ TkSpace ++ typ ++ TkAssgn
           ++ TkSpace ++ ppTerm t Γ
           ++ TkDot ++ TkCR)
  | CmdData (DefData name params kind ctors)  =>
    put (alist_add _ name kind Γ) ;;
    let s := runReader (ppDatatype name params kind ctors) Γ in
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

Local Close Scope string_scope.
Local Close Scope monad_scope.
