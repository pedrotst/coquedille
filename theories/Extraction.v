From Stdlib Require Extraction.
Extraction Language Haskell.
Require Import DenoteCoq.

Redirect "program.hs" Recursive Extraction denoteCoq.

From MetaRocq.Template Require Import All.

MetaRocq Quote Recursively Definition tst_syntax := nat.
Print tst_syntax.
