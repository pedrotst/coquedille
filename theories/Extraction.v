Require Coq.extraction.Extraction.
Extraction Language Haskell.
Require Import DenoteCoq.

Redirect "program.hs" Recursive Extraction denoteCoq.

Require Import MetaCoq.Template.All.

Quote Recursively Definition tst_syntax := nat.
Print tst_syntax.
