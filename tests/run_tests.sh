#!/usr/bin/env bash

coqc -Q ../theories Coquedille -Q ../coq-haskell/src Hask Extraction.v
mv main.hs.out main.hs
