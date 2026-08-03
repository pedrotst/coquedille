From MetaRocq.Template Require Import Ast AstUtils Loader.

(* Required after MetaRocq so that [string] is Rocq's and not MetaRocq's
   bytestring. *)
From Stdlib Require Import Program.Equality.
From Stdlib Require Import String.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Vectors.Vector.

Require Import Coquedille.Ast.
Require Import Coquedille.PrettyPrinter.
Require Import Coquedille.DenoteCoq.

Definition JMeq_rect' :=
fun (A : Type) (x : A) (P : A -> Type)
  (H : P x) (y : A) (H' : x ~= y) => true.

MetaRocq Quote Recursively Definition rect_syntax := JMeq.JMeq_rect.

Open Scope string_scope.

Eval compute in (pretty (denoteCoq rect_syntax)).
Eval compute in ((denoteCoq rect_syntax)).
