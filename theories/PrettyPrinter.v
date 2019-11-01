Require Import Coquedille.Ast.
Import Ced.

Require Import Coquedille.DenoteCoq.

Require Import List.
Require Import String.
Local Open Scope string.

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

(* ((t ·A) ·(S ·n)) *)

Instance PrettyType : Pretty Typ :=
  (fix pp barr bapp t :=
    match t with
    | TpArrowT t1 t2 => parens barr (pp true false t1 ++ TkSpace ++ TkArrow ++ TkSpace ++ pp false false t2)
    | TpPi name t1 t2 => TkPi ++ TkSpace ++ pretty name ++ TkSpace
                             ++ TkColon ++ TkSpace
                             ++ pp false false t1 ++ TkSpace
                             ++ TkDot ++ TkSpace ++ pp false false t2
    | TpApp t1 ts2 => parens bapp (pp false false t1 ++ TkSpace
                                     ++ TkTpDot ++ string_of_list_aux id (TkSpace ++ TkTpDot) (map (pp false true) ts2) 0)
    | TpVar v => v
    | KdStar => TkStar
    end) false false.

Fixpoint removeBindings (t: Typ) (n: nat) : Typ :=
match n with
| O => t
| S n' =>
  match t with
  | TpPi x t1 t2 => removeBindings t2 (pred n)
  | TpArrowT t1 t2 => removeBindings t2 (pred n)
  | _ => t
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
  | TpArrowT t1 t2 => TpArrowT (removeParams' t1) (removeParams' t2)
  | _ => t
  end.

(* Definition removeParams (t: Type) (data_name: Var) := removeParams' t data_name. *)

Definition ppctor params_count data_name ctor :=
  match ctor with
  | Ctr cname ty =>
    let no_bindings_t := removeBindings ty params_count in
    let no_params_t := removeParams data_name params_count no_bindings_t in
    TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ pretty no_params_t
  end.


(* Instance PrettyCtor : Pretty Ctor := *)
(*   fun ctor => *)
(*   match ctor with *)
(*   | Ctr cname ty => TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ pretty ty *)
(*   end. *)

Instance PrettyParams : Pretty Params :=
  fix pp params :=
    match params with
    | nil => ""
    | cons (n, t) ps =>
      TkSpace ++ TkOpenPar ++ n ++ TkSpace
              ++ TkColon ++ TkSpace ++ pretty t
              ++ TkClosePar ++ pp ps
    end.

Definition ppDatatype (name : Var) (params: Params) (kind : Typ) (ctors : list Ctor) :=
  TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ pretty kind ++ TkSpace ++ TkAssgn ++ TkCR
          ++ string_of_list (ppctor (List.length params) name) ctors 1 ++ TkDot.

(* Definition ppDatatype (name : Var) (params: Params) (kind : Typ) (ctors : list Ctor) := *)
  (* TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace *)
          (* ++ pretty kind ++ TkSpace ++ TkAssgn ++ TkCR *)
          (* ++ string_of_list pretty ctors 1 ++ TkDot. *)


Instance PrettyAssgn : Pretty Assgn :=
  fun asgn =>
    match asgn with
    | AssgnType name t => name ++ TkSpace ++ TkAssgn
                              ++ TkSpace ++ pretty t
                              ++ TkDot ++ TkCR
    | AssgnTerm name t => TkNotImpl
    end.

Instance PrettyCmd : Pretty Cmd :=
  fun c =>
    match c with
    | CmdAssgn def => pretty def ++ TkCR
    | CmdData (DefData name params kind ctors)  => ppDatatype name params kind ctors ++ TkCR
    end.

Instance PrettyProgram : Pretty Program :=
  fun p => string_of_list pretty p 0.

Instance PrettyOption {A} {x: Pretty A}: Pretty (option A) :=
  fun o =>
    match o with
      (* Maybe signal an error? *)
    | None => ""
    | Some x => pretty x
    end.

Local Close Scope string_scope.

