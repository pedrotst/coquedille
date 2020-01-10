Require Import Coq.Program.Equality.
Require Import String.
Require Import List. Import ListNotations.
Require Import Coq.Vectors.Vector.

Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.AstUtils.
Require Import MetaCoq.Template.Loader.

Require Import Coquedille.Ast.
Require Import Coquedille.PrettyPrinter.
Require Import Coquedille.DenoteCoq.

Definition JMeq_rect' :=
fun (A : Type) (x : A) (P : A -> Type)
  (H : P x) (y : A) (H' : x ~= y) => true.

(* Quote Recursively Definition JMeq_rect_syntax := JMeq_rect'. *)
Quote Recursively Definition rect_syntax := JMeq.JMeq_rect.

Open Scope string_scope.
(* Eval compute in (pretty (denoteCoq JMeq_rect_syntax)). *)
(* Eval compute in ((denoteCoq JMeq_rect_syntax)). *)

Eval compute in (pretty (denoteCoq rect_syntax)).
Eval compute in ((denoteCoq rect_syntax)).
