Require Import Coquedille.Ast.
Import Ced.

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
Definition TkTab     := "  ".
Definition TkAnon    := "anon".
Definition TkPi      := "Π".
Definition TkAll     := "∀".
Definition TkOpenPar := "(".
Definition TkClosePar:= ")".
Definition TkCR      := "
".

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

Definition string_of_list {A} (f : A -> string) (l : list A): string :=
  string_of_list_aux f TkCR l 1.

Fixpoint ppKind (k : Ced.Kind) :=
  match k with
  | Ced.KdStar => TkStar
  | Ced.KdArrow k1 k2 => ppKind k1 ++ TkSpace ++ TkArrow ++ TkSpace ++ ppKind k2
  | Ced.KdPi k t => TkNotImpl
  end.

Definition ppName (name : Name) :=
  match name with
  | Anon => TkAnon
  | Named v => v
  end.

     (* = [CmdData *)
     (*      (DefData "option" KdStar *)
     (*         [Ctr "Some" *)
     (*            (TpPi (cName "A") (TpVar "x") *)
     (*               (TpPi cAnon (TpVar "x") (TpVar "x"))); *)
     (*         Ctr "None" (TpPi (cName "A") (TpVar "x") (TpVar "x"))])] *)
     (* : CedProgram *)
Fixpoint ppType (t : Typ) :=
  match t with
  | TpArrowT t1 t2 => ppType t1 ++ TkArrow ++ ppType t2
  | TpPi name t1 t2 => TkPi ++ TkSpace ++ ppName name ++ TkSpace
                            ++ TkColon ++ TkSpace
                            ++ ppType t1 ++ TkSpace
                            ++ TkDot ++ TkSpace ++ ppType t2
  | TpVar v => v
  | _ => TkNotImpl
  end.

Fixpoint ppCtor (ctor : Ctor) :=
  match ctor with
  | Ctr cname ty => TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ ppType ty
  end.

Definition ppDatatype (name : Var) (kind : Kind) (ctors : list Ctor) :=
"data " ++ name ++ " : " ++ ppKind kind ++ " := " ++ TkCR
        ++ string_of_list ppCtor ctors ++ TkDot.

(* Eval compute in (ppDatatype ("Pedro")). *)

Definition ppCmd (c : Cmd) : string :=
  match c with
  | CmdAssgn def => TkNotImpl
  | CmdData (DefData v k ctors)  => ppDatatype v k ctors ++ TkCR
  end.

Definition ppProgram (p : Program) :=
  string_of_list ppCmd p.

Local Close Scope string_scope.
