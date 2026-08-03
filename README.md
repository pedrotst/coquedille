# Coquedille [![CI](https://github.com/pedrotst/coquedille/actions/workflows/ci.yml/badge.svg)](https://github.com/pedrotst/coquedille/actions/workflows/ci.yml)

This project will translate [Rocq](https://rocq-prover.org/) (formerly Coq) terms
into [Cedille](https://cedille.github.io/) terms.

This project currently compiles with Rocq 9.2.0, with dependencies of
[MetaRocq](https://github.com/MetaRocq/metarocq) (formerly metacoq), and
[coq-ext-lib](https://github.com/coq-community/coq-ext-lib).

## Building

Create a switch with the dependencies:

```bash
opam switch create coquedille ocaml-base-compiler.5.3.0 --repos=rocq-released=https://rocq-prover.org/opam/released,default=https://opam.ocaml.org
```

```bash
opam install --switch=coquedille rocq-core.9.2.0 rocq-stdlib rocq-metarocq-template.1.5.1+9.2 coq-ext-lib
```

Then build with `./init_repo.sh`, or directly:

```bash
coq_makefile -f _CoqProject -o Makefile && make
```

## Tests

The test suite extracts the translator to Haskell and diffs its output against
the expected Cedille rendering of each case, so it needs `ghc` on the `PATH`.

```bash
cd tests && ./run_tests.sh
```
