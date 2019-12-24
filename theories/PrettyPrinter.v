Require Import Coquedille.Ast.
Import Ced.

Require Import List.
Require Import String.
Local Open Scope string.

Require Import Coquedille.DenoteCoq.
(* Require Import Coquedille.Utils. *)

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Applicative.
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
Definition TkULam       := "Λ".
Definition TkAssgn     := "=".
Definition TkCR        := "
".

Class Pretty (p : Type) :=
  pretty : p -> string.


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


Local Open Scope monad_scope.
(* We can simplify this to a simple list and mark what lives on the kind level *)
Definition type_ctx := alist Var (Kind + Typ).

Definition string_eq x y := utils.string_compare x y = Eq.

Instance string_RelDec : RelDec.RelDec string_eq :=
  { rel_dec := String.eqb }.

Definition alist_app {B} (a1 a2: alist string B) : alist string B :=
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

Definition getVar (t: TTy): option Var :=
  match t with
  | inr t' => match t' with | TVar v => Some v | _ => None end
  | inl t' => match t' with | TyVar v => Some v | _ => None end
  end.

Definition ppDot (t: TTy) : reader type_ctx string :=
  Γ <- ask ;;
  match getVar t with
  | None => ret ""
  | Some v =>
      match alist_find _ v Γ with
      | None => ret ""
      | Some t =>
        match t with
        | inl _ => ret TkTDot
        | _ => ret ""
        end
      end
  end.

Fixpoint ppKind' (ki : Kind) : reader type_ctx string :=
  match ki with
  | KdStar => ret TkStar
  | KdAll x k1 k2 =>
    k1' <- match k1 with
          | inl ki1 => ppKind' ki1
          | inr ty1 => ppTyp' false false ty1
          end ;;
    k2' <- ppKind' k2 ;;
    match x with
    | Anon => ret (k1' ++ TkSpace ++ TkArrow ++ TkSpace ++ k2')
    | Named name => ret (TkAll ++ TkSpace ++ name ++ TkSpace
                              ++ TkColon ++ TkSpace ++ k1'
                              ++ TkSpace ++ TkDot ++ TkSpace ++ k2')
    end
  end

with ppTyp' (barr bapp: bool) (t : Typ) : reader type_ctx string :=
  match t with
  | TyApp t1 ts2 =>
    t1' <- ppTyp' false true t1 ;;
    let ppApp (t: TTy) : reader type_ctx string :=
        d <- ppDot t ;;
        match t with
        | inr t' =>
          t'' <- ppTerm' false true t' ;;
          ret (d ++ t'')
        | inl t' =>
          t'' <- ppTyp' false false t' ;;
          ret (d ++ t'')
        end in
    ts2' <- list_m (map ppApp ts2) ;;
    ret (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
  | TyPi x t1 t2 =>
    match x with
    | Anon =>
      t1' <- ppTyp' true false t1 ;;
      t2' <- ppTyp' false false t2 ;;
      ret (parens barr (t1' ++ TkSpace ++ TkArrow ++ TkSpace ++ t2'))
    | Named name =>
      t1' <- ppTyp' false false t1 ;;
      t2' <- local (fun Γ => alist_add _ name (inr t1) Γ) (ppTyp' false false t2) ;;
      ret (TkPi ++ TkSpace ++ name ++ TkSpace
                ++ TkColon ++ TkSpace
                ++ t1' ++ TkSpace
                ++ TkDot ++ TkSpace ++ t2')
    end
  | TyAll x t1 t2 =>
    let name := match x with | Anon => "_" | Named n => n end in
    k <- ppKind' t1 ;;
    t2' <- local (fun Γ => alist_add _ name (inl t1) Γ) (ppTyp' false false t2) ;;
    ret (TkAll ++ TkSpace ++ name ++ TkSpace ++ TkColon
               ++ TkSpace ++ k ++ TkSpace ++ TkDot ++ TkSpace ++ t2')
  | TyLam x t1 t2 =>
    let name := match x with | Anon => "_" | Named n => n end in
    t1' <- ppTyp' false false t1 ;;
    t2' <- local (fun Γ => alist_add _ name (inr t1) Γ) (ppTyp' false false t2) ;;
    ret (TkLam ++ TkSpace ++ name ++ TkSpace ++ TkColon
               ++ TkSpace ++ t1' ++ TkSpace ++ TkDot ++ TkSpace ++ t2')
  | TyVar v => ret v
  | _ => ret "?"
  end

with ppTerm' (barr bapp: bool) (t : Term): reader type_ctx string :=
  match t with
  | TApp t1 ts2 =>
    t1' <- ppTerm' false true t1 ;;
    let ppApp (t: TTy) : reader type_ctx string :=
        d <- ppDot t ;;
        match t with
        | inr t' =>
          t'' <- ppTerm' false true t' ;;
          ret (d ++ t'')
        | inl t' =>
          t'' <- ppTyp' false false t' ;;
          ret (d ++ t'')
        end in
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
  | TLamK x k t =>
    k' <- ppKind' k ;;
    t' <- ppTerm' false false t ;;
    let x' := match x with | Anon => "_" | Named y => y end in
    ret (parens bapp (TkLam ++ TkSpace ++ x' ++ TkSpace
                            ++ TkColon ++ TkSpace ++ k' ++ TkSpace
                            ++ TkDot ++ TkSpace ++ t'))
  | TLamT x ty t =>
    ty' <- ppTyp' false false ty ;;
    t' <- ppTerm' false false t ;;
    let x' := match x with | Anon => "_" | Named y => y end in
    ret (parens bapp (TkLam ++ TkSpace ++ x' ++ TkSpace
                            ++ TkColon ++ TkSpace ++ ty' ++ TkSpace
                            ++ TkDot ++ TkSpace ++ t'))
  end.

Definition ppKind (ki: Kind) (Γ : type_ctx) :=
  (@runReader _ _ (ppKind' ki) Γ).

Definition ppTyp (t: Typ) (Γ : type_ctx) :=
  (@runReader _ _ (ppTyp' false false t) Γ).

Definition ppTerm (t: Term) (Γ : type_ctx) :=
  (@runReader _ _ (ppTerm' false false t) Γ).

Fixpoint removeBindingsTyp (t: Typ) (n: nat) : state type_ctx Typ :=
match n with
| O => ret t
| S n' =>
  match t with
  | TyPi x t1 t2 =>
    Γ <- get ;;
    t' <- removeBindingsTyp t2 (pred n);;
    match x with
    | Anon => ret t'
    | Named name =>
      put ((name, inr t1) :: Γ) ;;
      ret t'
    end
  | TyAll x k t2 =>
    Γ <- get ;;
    t' <- removeBindingsTyp t2 (pred n);;
    match x with
    | Anon => ret t'
    | Named name =>
      put ((name, inl k) :: Γ) ;;
      ret t'
    end
  | _ => ret t
  end
end.

Fixpoint removeBindingsK (k: Kind) (n: nat) : state type_ctx Kind :=
match n with
| O => ret k
| S n' =>
  match k with
  | KdAll x k1 k2 =>
    Γ <- get ;;
    k' <- removeBindingsK k2 (pred n);;
    match x with
    | Anon => ret k'
    | Named name =>
      put ((name, k1) :: Γ) ;;
      ret k'
    end
  | _ => ret k
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
  | TyApp t nil => t
  | _ => t
  end.

Fixpoint removeParams (data_name : Var) (params_count: nat) (t: Typ): Typ :=
  let removeParams' := removeParams data_name params_count in
  match t with
  | TyApp t1 ts2 =>
    (* let rs := map removeParams' ts2 in *)
    match t1 with
    | TyVar v =>
      if (string_dec v data_name)
      then let rs' := removeN ts2 params_count in
           flattenApp (TyApp t1 rs')
      else flattenApp (TyApp t1 ts2)
    | _ => TyApp (removeParams' t1) ts2
    end
  | TyPi x t1 t2 => TyPi x (removeParams' t1) (removeParams' t2)
  | _ => t
end.

Definition ppctor (params_count: nat) (data_name: Var) (ctor: Ctor): reader type_ctx string :=
  match ctor with
  | Ctr cname ty =>
    Γ <- ask ;;
    let '(no_bindings_t, Γ') := runState (removeBindingsTyp ty params_count) Γ in
    (* Apps with the constructor in cedille doesn't explicitely show the parameters *)
    let no_params_t := removeParams data_name params_count no_bindings_t in
    t' <- local (fun _ => (alist_app Γ Γ')) (ppTyp' false false no_params_t) ;;
    (* t' <- ppTyp' false false ty ;; *)
    ret (TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ t')
  end.

Instance PrettyParams : Pretty Params :=
  fix pp params :=
    match params with
    | nil => ""
    | cons (n, t) ps =>
      let t' := match t with | inl k => ppKind k nil | inr ty => ppTyp ty nil end in
      TkSpace ++ TkOpenPar ++ n ++ TkSpace
              ++ TkColon ++ TkSpace ++ t'
              ++ TkClosePar ++ pp ps
    end.

Program Definition ppDatatype (name : Var) (params: Params) (ki : Kind) (ctors : list Ctor) : reader type_ctx string :=
  Γ <- ask ;;
  (* let '(k, _) := runState (removeBindingsK ki (List.length params)) nil in *)
  kind <- ppKind' ki ;;
  (* Working on the reader monad here makes the mapping trivial *)
  ctorlist <- list_m (map (ppctor (List.length params) name) ctors) ;;
  let ctors' := string_of_list id ctorlist 1 in
  ret (TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ kind ++ TkSpace ++ TkAssgn ++ TkCR
          ++ ctors' ++ TkDot).

Definition ppmKind (v: Var) (mki : option Kind) : state type_ctx string :=
  match mki with
  | None => ret ""
  | Some ki =>
    Γ <- get ;;
    put (alist_add _ v (inl ki) Γ);;
    ret (TkColon ++ TkSpace ++ ppKind ki Γ ++ TkSpace)
  end.

Definition ppmType (v: Var) (mty : option Typ) : state type_ctx string :=
  match mty with
  | None => ret ""
  | Some ty =>
    Γ <- get ;;
    put (alist_add _ v (inr ty) Γ);;
    ret (TkColon ++ TkSpace ++ ppTyp ty Γ ++ TkSpace)
  end.

Program Definition ppCmd (c: Cmd): state type_ctx string :=
  Γ <- get ;;
  match c with
  | CmdAssgn (AssgnTerm v mty t) =>
    typ <- ppmType v mty ;;
    ret (v ++ TkSpace ++ typ ++ TkAssgn
           ++ TkSpace ++ ppTerm t Γ
           ++ TkDot ++ TkCR)
  | CmdAssgn (AssgnType v mki t) =>
    ki <- ppmKind v mki ;;
    ret (v ++ TkSpace ++ ki ++ TkAssgn
           ++ TkSpace ++ ppTyp t Γ
           ++ TkDot ++ TkCR)
  | CmdData (DefData name params kind ctors)  =>
    put (alist_add _ name (inl kind) Γ) ;;
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
