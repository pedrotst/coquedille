#!/usr/bin/env bash

git submodule update --init
cd coq-haskell
coq_makefile -f _CoqProject -o Makefile
make
