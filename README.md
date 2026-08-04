# Coquedille [![CI](https://github.com/pedrotst/coquedille/actions/workflows/ci.yml/badge.svg)](https://github.com/pedrotst/coquedille/actions/workflows/ci.yml)

This project will translate [Rocq](https://rocq-prover.org/) (formerly Coq) terms
into [Cedille](https://cedille.github.io/) terms.

This project currently compiles with Rocq 9.0.0, with dependencies of
[MetaRocq](https://github.com/MetaRocq/metarocq) (formerly metacoq),
[coq-ext-lib](https://github.com/coq-community/coq-ext-lib) and
[Autosubst](https://github.com/uds-psl/autosubst-ocaml).

### Why 9.0

The Rocq version is pinned by Autosubst, not by this translator: the only
Rocq-era package, `rocq-autosubst-ocaml.1.1+9.0`, requires
`rocq-core >= 9.0 & < 9.1` *and* `ocaml >= 4.09 & < 4.15`. So the switch has to
be Rocq 9.0 on an OCaml 4.14 compiler; 9.1 and 9.2 are not options while
Autosubst is a dependency. MetaRocq and ext-lib follow from that: `1.4+9.0` is
the MetaRocq for 9.0, and ext-lib caps at `0.13.0` below `coq-core 9.2`.

The translator itself is version-agnostic here — it builds unmodified on 9.0 and
9.2 alike, since MetaRocq's `term` type is identical between `1.4+9.0` and
`1.5.1+9.2`.

## Building

Create a switch with the dependencies:

```bash
opam switch create coquedille-9.0 ocaml-base-compiler.4.14.2 --repos=rocq-released=https://rocq-prover.org/opam/released,default=https://opam.ocaml.org
```

```bash
opam install --switch=coquedille-9.0 rocq-core.9.0.0 rocq-stdlib coq-ext-lib.0.13.0 rocq-metarocq-template.1.4+9.0 rocq-autosubst-ocaml.1.1+9.0
```

Then build with `./init_repo.sh`, or directly:

```bash
coq_makefile -f _CoqProject -o Makefile && make
```

## Tests

The test suite extracts the translator to Haskell and diffs its output against
the expected Cedille rendering of each case, so it needs `ghc` on the `PATH`.
`theories/` must be built first — the harness does not build it.

```bash
cd tests && ./run_tests.sh
```

The `tests/*/expected` files are tied to the Rocq version: standard lemmas such
as `eq_ind` carry different binder names across releases, so the rendering of
`zeroneqS` differs between 9.0 and 9.2 by pure α-renaming. They are recorded
here for 9.0.
