Require Import Coquedille.Ast.
Import Ced.

Require Import Coquedille.DenoteCoq.

Require Import String.
Local Open Scope string.

(* Token Definitions *)
Definition TkNotImpl := "Just a dummy token".
Definition TkStar    := "★".
Definition TkArrow   := "➔".
Definition TkSpace   := " ".
Definition TkColon   := ":".
Definition TkPipe    := "|".
Definition TkDot     := ".".
Definition TkTab     := "  ".
Definition TkAnon    := "anon".
Definition TkPi      := "Π".
Definition TkAll     := "∀".
Definition TkOpenPar := "(".
Definition TkClosePar:= ")".
Definition TkAssgn   := ":=".
Definition TkTpDot   := "·".
Definition TkData    := "data".
Definition TkCR      := "
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

Instance PrettyType : Pretty Typ :=
  fix pp t :=
    match t with
    | TpArrowT t1 t2 => pp t1 ++ TkSpace ++ TkArrow ++ TkSpace ++pp t2
    | TpPi name t1 t2 => TkPi ++ TkSpace ++ pretty name ++ TkSpace
                             ++ TkColon ++ TkSpace
                             ++ pp t1 ++ TkSpace
                             ++ TkDot ++ TkSpace ++ pp t2
    | TpApp t1 t2 => pp t1 ++ TkSpace ++ TkTpDot ++ pp t2
    | TpVar v => v
    | KdStar => TkStar
    end.

Instance PrettyCtor : Pretty Ctor :=
  fun ctor =>
  match ctor with
  | Ctr cname ty => TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ pretty ty
  end.

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
          ++ string_of_list pretty ctors 1 ++ TkDot.


Instance PrettyDatatype : Pretty Cmd :=
  fun c =>
    match c with
    | CmdAssgn def => TkNotImpl
    | CmdData (DefData name params kind ctors)  => ppDatatype name params kind ctors ++ TkCR
    end.

Instance PrettyProgram : Pretty Program :=
  fun p => string_of_list pretty p 0.

Local Close Scope string_scope.
