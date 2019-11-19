Require Import Coquedille.Ast.
Import Ced.

Require Import List.
Require Import String.
Local Open Scope string.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.
Require Import Hask.Data.List.
Require Import Hask.Data.Maybe.

Require Import Coquedille.DenoteCoq.
Require Import Coquedille.Utils.

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

(* Instance PrettyType : Pretty Typ := *)
(*   (fix pp barr bapp t := *)
(*     match t with *)
(*     (* | TpArrowT t1 t2 => parens barr (pp true false t1 ++ TkSpace ++ TkArrow ++ TkSpace ++ pp false false t2) *) *)
(*     | TpPi name t1 t2 => TkPi ++ TkSpace ++ pretty name ++ TkSpace *)
(*                              ++ TkColon ++ TkSpace *)
(*                              ++ pp false false t1 ++ TkSpace *)
(*                              ++ TkDot ++ TkSpace ++ pp false false t2 *)
(*     | TpApp t1 ts2 => parens bapp (pp false false t1 ++ TkSpace *)
(*                                      ++ TkTpDot ++ string_of_list_aux id (TkSpace ++ TkTpDot) (map (pp false true) ts2) 0) *)
(*     | TpVar v => v *)
(*     | KdStar => TkStar *)
(*     end) false false. *)

Fixpoint ppTerm' (barr bapp: bool) (t : Typ): State type_ctx string :=
    match t with
    | TpPi x t1 t2 =>
      match x with
      | Anon =>
        Γ <- get ;
        t1' <- ppTerm' true false t1 ;
        put Γ ;;
        t2' <- ppTerm' false false t2 ;
        pure (parens barr (t1' ++ TkSpace ++ TkArrow ++ TkSpace ++ t2'))
      | Named name =>
        Γ <- get ;
        t1' <- ppTerm' false false t1 ;
        put ((name, t1) :: Γ) ;;
        t2' <- ppTerm' false false t2 ;
        pure (TkPi ++ TkSpace ++ name ++ TkSpace
                             ++ TkColon ++ TkSpace
                             ++ t1' ++ TkSpace
                             ++ TkDot ++ TkSpace ++ t2')
      end
    | TpApp t1 ts2 =>
      Γ <- get ;
      t1' <- ppTerm' false false t1 ;
      let ppApp (t: Typ) :=
          (match t with
           | TpVar n =>
             match ctx_find n Γ with
             | None => ""
             | Some t =>
               match t with
               | KdStar => TkTpDot
               | _ => ""
               end
             end
           | _ => ""
          end) ++ fst (ppTerm' false true t nil) in
      (* let ts2' := map fst (map (fun t => ppTerm' false true t nil) ts2) in *)
      let ts2' := (map ppApp ts2) in
      pure (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
    | TpVar v => pure v
    | KdStar => pure TkStar
    end.

Definition ppTerm (t: Typ) (Γ : type_ctx) :=
  fst (ppTerm' false false t Γ).


Fixpoint removeBindings (t: Typ) (n: nat) : State type_ctx Typ :=
match n with
| O => pure t
| S n' =>
  match t with
  | TpPi x t1 t2 =>
    Γ <- get ;
    t' <- removeBindings t2 (pred n);
    match x with
    | Anon => pure t'
    | Named name =>
      put ((name, t1) :: Γ) ;;
      pure t'
    end
  | _ => pure t
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

Definition ppctor params_count (Γ: type_ctx) data_name ctor :=
  match ctor with
  | Ctr cname ty =>
    let '(no_bindings_t, Γ') := removeBindings ty params_count nil in
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

Definition ppDatatype (name : Var) (params: Params) (kind : Typ) (ctors : list Ctor) Γ :=
  TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ ppTerm kind Γ ++ TkSpace ++ TkAssgn ++ TkCR
          ++ string_of_list (ppctor (List.length params) Γ name) ctors 1 ++ TkDot.


Instance PrettyAssgn : Pretty Assgn :=
  fun asgn =>
    match asgn with
    | AssgnType name t => name ++ TkSpace ++ TkAssgn
                              ++ TkSpace ++ ppTerm t nil
                              ++ TkDot
    | AssgnTerm name t => TkNotImpl
    end.

(* Instance PrettyCmd : Pretty Cmd := *)
(*   fun c => *)
(*     match c with *)
(*     | CmdAssgn def => pretty def ++ TkCR *)
(*     | CmdData (DefData name params kind ctors)  => ppDatatype name params kind ctors ++ TkCR *)
(*     end. *)

Definition ppCmd (c: Cmd): State type_ctx string :=
    match c with
    | CmdAssgn def => pure (pretty def)
    | CmdData (DefData name params kind ctors)  =>
      Γ <- get ;
      let s := ppDatatype name params kind ctors Γ ++ TkCR in
      put ((name, kind) :: Γ) ;;
      pure s
    end.

Fixpoint ppProgram' (p : Program) : State type_ctx string :=
  match p with
  | nil => pure ""
  | c :: cs =>
    c' <- ppCmd c;
    cs' <- ppProgram' cs;
    pure (c' ++ TkCR ++ cs')
  end.

(* Instance PrettyProgram : Pretty Program := *)
  (* fun p => string_of_list pretty p 0. *)

Instance PrettyProgram : Pretty Program :=
  fun p => fst (ppProgram' p nil).

Instance PrettyOption {A} {x: Pretty A}: Pretty (option A) :=
  fun o =>
    match o with
      (* Maybe signal an error? *)
    | None => ""
    | Some x => pretty x
    end.

Local Close Scope string_scope.

