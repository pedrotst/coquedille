Require Import MetaCoq.Template.All.

Quote Recursively Definition nat_syntax := nat.

Inductive myNat : Type :=
| z : myNat
| s : myNat -> myNat.

Quote Recursively Definition myNat_syntax := myNat.

Print nat_syntax.
