Require Import Coquedille.Ast.
Require Import Coquedille.DenoteCoq.

Require Import String.

Local Open Scope string.
(* Token Definitions *)
Definition TkNotImpl := "TOKEN NOT IMPLEMENTED!!".
Definition TkStar    := "★".
Definition TkArrow   := "➔".
Definition TkSpace   := " ".
Definition TkColon   := ":".
Definition TkPipe    := "|".
Definition TkDot     := ".".
Definition TkCR      := "
".

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  string_of_list_aux f TkCR l.

Fixpoint ppKind (k : CedKind) :=
  match k with
  | KdStar => TkStar
  | KdArrow k1 k2 => ppKind k1 ++ TkSpace ++ TkArrow ++ TkSpace ++ ppKind k2
  | KdPi k t => TkNotImpl
  end.

Fixpoint ppType (t : CedType) :=
  match t with
  | TpArrowT t1 t2 => ppType t1 ++ TkArrow ++ ppType t2
  | TpVar v => v
  | _ => TkNotImpl
  end.

Fixpoint ppCtor (ctor : CedCtor) :=
  match ctor with
  | Ctr v t => TkPipe ++ v ++ TkColon
  end.

Definition ppDatatype (name : Var) (kind : CedKind) (ctors : list CedCtor) :=
"data " ++ name ++ " : " ++ ppKind kind ++ " := " ++ TkCR
        ++ string_of_list ppCtor ctors ++ TkDot.

(* Eval compute in (ppDatatype ("Pedro")). *)

Definition ppCmd (c : CedCmd) : string :=
  match c with
  | CmdDef def => TkNotImpl
  | CmdData (DefData v k ctors)  => ppDatatype v k ctors ++ TkCR
  end.

Definition ppProgram (p : CedProgram) :=
  AstUtils.string_of_list ppCmd p.

Local Close Scope string_scope.
