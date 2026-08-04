# PLAN — CDLE in Rocq: elaboration from Ced, and the strength theorem

This replaces the Rocq-9.2 porting plan, which is complete (merged as PR #34;
the old plan text lives in git history). Two goals, in order:

1. **Elaboration**: a translation from coquedille's internal Cedille AST
   (`Ced.*` in `theories/Ast.v`) into a formalized **CDLE** (Cedille Core),
   mechanized in this repo.
2. **Strength theorem**: Rocq has strictly greater arithmetical /
   proof-theoretic strength than CDLE.

The document is definition-first: §1 fixes every object, §2 states the
theorems as formulas, §3–§10 are the milestones M0–M7, §11 risks, §12 ground
rules.

---

## 1. The objects

### 1.1 What is CDLE here?

The Calculus of Dependent Lambda Eliminations as given by the **Cedille Core
specification** (Stump's cedille-core), i.e. the post-lifting formulation:

- syntax: kinds `κ`, types `T`, annotated terms `t`, pure (erased) terms `e`;
- erasure `|t|` from annotated terms to pure λ-terms;
- primitives beyond an impredicative CC core: dependent intersection
  `ι x:T. T'`, implicit product `∀ x:T. T'`, untyped equality `{e ≃ e'}` with
  introduction `β`, rewriting `ρ`, contradiction `δ`, cast `φ`;
- judgments: `Γ ⊢ t : T`, with conversion modulo β on erasures.

**M0 pins the exact rule set** (which spec revision, whether ς/symmetry is a
primitive, treatment of global definitions). Every departure from the pinned
spec goes in `DIVERGENCES.md` — before the code that embodies it, never after.

### 1.2 What is Ced, and what is the gap?

The AST in `theories/Ast.v`: stratified `Kind`/`Typ`/`Term` with **named**
variables, plus surface-level constructs CDLE does not have:

| Ced construct | CDLE status |
|---|---|
| `TVar/TLam/TApp/TyPi/TyAll/TyIntersec/TyEq/TDelta/TRho/TBeta` | direct counterpart |
| `TLetTm/TLetTy` | absent — encode as β-redex / substitute away |
| `TMu` (σ case / μ recursion, motive + branches) | absent — elaborate to encoded case/recursor |
| `CmdData` (datatype declarations) | absent — elaborate to λ-encodings (Mendler + ι) |
| unannotated binders (`TLam _ _ None _`, emitted by `bind_nrargs`) | CDLE terms are fully annotated |
| named variables | de Bruijn in the formalization |

So "translation Ced → CDLE" = **the datatype/pattern-matching elaboration**,
the same job Cedille 1.x's own elaborator does (blueprints: the Firsov–Stump
generic induction derivation and the Jenkins–Stump datatype-elaboration line).

### 1.3 Arithmetic sentences and Arith(T)

Fix a deep embedding of first-order arithmetic in Rocq: a syntax type `form`
and Tarski truth `⟦φ⟧ℕ : Prop` over Rocq's `nat`. Fix canonical
interpretations:

- `φ ↦ φ̂` : arithmetic into CDLE, via the λ-encoded naturals **produced by the
  M2 datatype elaboration** (zero, succ, derived induction);
- `φ ↦ ⟦φ⟧ℕ` : arithmetic into Rocq via `nat`.

```
Arith(CDLE) := { φ | CDLE ⊢ φ̂ }          Arith(Rocq) := { φ | Rocq ⊢ ⟦φ⟧ℕ }
```

### 1.4 Consistency, two forms

```
⊥ := ∀ X : ★ . X

Con(CDLE)  (internal)    := ¬ ∃ t,  ⊢ t : ⊥                       -- about the Inductive judgment
Con(CDLE)  (arithmetic)  := ¬ ∃ n : nat, Proof_CDLE(n, ⌜⊥⌝)       -- Gödel-coded
```

The internal form is what the model proves directly (M4); the arithmetic form
is what makes `Con(CDLE)` a member of `Arith(Rocq)` (M5) and the input to
Gödel II (M7).

## 2. The theorems

**Main theorem (strength).**

```
Arith(CDLE) ⊊ Arith(Rocq)
```

decomposed into three obligations:

```
O1 (inclusion)   ∀ φ,  CDLE ⊢ φ̂  →  Rocq ⊢ ⟦φ⟧ℕ        [mechanized: M3 model + M6 adequacy]
O2 (witness ⊢)   Rocq ⊢ Con(CDLE)                        [mechanized: M3 + M4 + M5]
O3 (witness ⊬)   CDLE ⊬ Con(CDLE)                        [paper: Gödel II, hypotheses verified, M7]
```

O1 + O2 + O3 ⟹ `Con(CDLE) ∈ Arith(Rocq) \ Arith(CDLE)` ⟹ strict inclusion.

**Elaboration theorems (the Ced → CDLE deliverable).**

```
E1 (totality)      Supported(p)  →  ∃ c, elab(p) = inr c
E2 (scope safety)  elab(p) = inr c  →  well_scoped(c)
E3 (preservation)  elab claims c : T  →  ⊢ c : T  in the formal CDLE     [stretch]
```

Dependencies: O1–O3 need M0, M1, M3–M7; the elaboration M2 is scheduled
**first** because it is the user-facing deliverable and because its Stage B
supplies the encoded-nat package that `φ̂` in §1.3 is defined from.

## 3. M0 — Baseline and spec pinning (days)

1. Verify the baseline at HEAD: `make` and `cd tests && ./run_tests.sh` green
   in the `coquedille-9.0` switch (the 9.2 port is merged, but the repo has
   since been pinned back to Rocq 9.0 so that Autosubst can be a direct
   dependency — see §4; CI runs on GitHub Actions).
2. Vendor the Cedille Core spec (a fixed revision) into `doc/`, transcribe the
   rule set into a reference section, and decide:
   - **D1** the exact primitive equality rules (β, ρ, δ, φ; is ς primitive?);
   - **D2** stratified syntax — recommended: yes, matching both the spec and
     `Ced`'s `Kind`/`Typ`/`Term`;
   - **D3** global definitions inside CDLE judgments — recommended: yes,
     matching `Ced.Program`; consistency handles them via a substitution lemma.
3. Create `DIVERGENCES.md`.
4. Port the persistent-session tooling (`tools/cq-start`, `tools/cq`,
   `tools/preamble.v`) from gadt_translation, retargeted at this repo's
   switch. All development below goes through it — no `coqc` iteration.

## 4. M1 — CDLE syntax, erasure, typing in Rocq (2–4 weeks)

- `autosubst/cdle.sig` + generation script. The version tension is **resolved by
  pinning the repo to Rocq 9.0** rather than by vendoring: `rocq-autosubst-ocaml`
  requires `rocq-core >= 9.0 & < 9.1` and `ocaml < 4.15`, so the switch is
  Rocq 9.0 on OCaml 4.14.2 and Autosubst is an ordinary direct dependency. The
  generator runs in the same switch as the build; no cross-switch vendoring
  step, and no need to verify generated output against a second Rocq. Cost of
  the pin: 9.1/9.2 are closed off while Autosubst is a dependency.
- `theories/CDLE/Syntax.v` — well-scoped de Bruijn kinds/types/annotated terms
  + pure terms `e` (**D4**: de Bruijn via Autosubst, recommended).
- `theories/CDLE/Erasure.v` — `|·|` and its substitution-commutation lemmas.
- `theories/CDLE/Reduction.v` — β on pure terms, and **confluence**: δ's
  soundness ultimately rests on `λx.λy.x ≠β λx.λy.y`, which needs
  Church–Rosser.
- `theories/CDLE/Typing.v` — `Γ ⊢ t : T` as an `Inductive`, conversion modulo
  erasure per the pinned spec.
- `theories/CDLE/Checker.v` — a **sound** (not necessarily complete) decidable
  checker: `check Γ t T = true → Γ ⊢ t : T`. This is M2's validation
  instrument: elaborated output can be *run* through it.

Checkpoint: hand-write closed CDLE terms (Church nats; the ι-based induction
package for booleans) and validate them with `Checker`.

## 5. M2 — Elaboration `Ced → CDLE` (staged; Stage A 1–2 weeks, C open-ended)

- **Stage A — direct fragment.** `theories/Elab.v`: named → de Bruijn,
  scope-checked, covering the direct-counterpart rows of §1.2 plus lets.
  Erased/implicit applications follow the `(bool * TyTerm)` application lists.
  Everything else is a *checked error*, not a silent drop.
  Theorems: E1 restricted to the direct fragment, E2.
- **Stage B — hardcoded datatype packages.** Elaborate `CmdData`/`TMu` for the
  concrete datatypes the test suite exercises (`nat`, `list`, `option`,
  `vector`, `eq`) via hand-written encoding packages (Mendler/Church + ι
  induction), in the spirit of `theories/Hardcoded.v`. σ (non-recursive `TMu`)
  → encoded case; μ (recursive) → derived recursor. Validate by running the 13
  golden tests through `denoteCoq ∘ elab ∘ Checker`.
  Stage B's nat package is what §1.3's `φ̂` is built from.
- **Stage C — generic datatype elaboration** (Firsov–Stump / Jenkins–Stump
  style), replacing the hardcoded packages. Hard and open-ended; **not** on
  the critical path for O1–O3 (only nat's package is needed there).
- **Stage D (stretch)** — E3: the verified elaborator.

Boundary problems in coquedille's output — the elaborator checks and rejects,
with upstream fixes in `DenoteCoq.v` where cheap:

- unannotated binders from `bind_nrargs` (`TLam … None …`);
- the non-fresh `fresh` (`theories/DenoteCoq.v:346`, single-prime append) —
  E2's scope check guards against the capture it can cause;
- the `delparamsTy` equation bug (`theories/DenoteCoq.v:599`: `TyEq` rebuilt
  from `t1` twice) — fix before trusting translated equations.

## 6. M3 — Realizability model of CDLE in Rocq (2–3 months)

`theories/CDLE/Model.v`. Semantic universe:

```
⟦★⟧                  := Λ → Prop          (Λ = pure terms; impredicative Prop hosts ★)
⟦Π x:T.κ⟧, ⟦Π X:κ.κ'⟧ := Type-level function spaces
```

Type interpretations, all **closed under =β** (the one closure condition, and
exactly what makes φ sound):

```
⟦∀ x:T. T'⟧ρ  := intersection over all instances (implicit: one realizer for all)
⟦ι x:T. T'⟧ρ  := λ e. e ∈ ⟦T⟧ρ ∧ e ∈ ⟦T'⟧(ρ, x↦e)
⟦{e₁ ≃ e₂}⟧ρ  := if |e₁|ρ =β |e₂|ρ then Λ else ∅
```

Fundamental theorem (soundness), by induction on derivations:

```
Γ ⊢ t : T   →   ∀ ρ ⊨ Γ,   |t|ρ ∈ ⟦T⟧ρ
```

δ's case needs M1's confluence; ρ and φ need the equality semantics and
=β-closure. Design freedom: only soundness is needed, never completeness — the
semantics is chosen to make the rules easy.

## 7. M4 — Consistency, internal form (short, given M3)

```
Theorem cdle_consistent : ¬ ∃ t, ⊢ t : ⊥.
```

`⟦⊥⟧ = ⋂_{S : Λ→Prop} S = ∅` (instantiate with `fun _ => False`); soundness
would put a realizer in ∅. This is O2 in internal form.

## 8. M5 — Arithmetization of Con (weeks, tedious)

Gödel-code CDLE syntax and derivations as `nat` inside Rocq; prove the coding
adequate: `Proof_CDLE(n, ⌜⊥⌝) ↔ ∃ d, …`. Transfers M4 to the arithmetic
`Con(CDLE)` of §1.4 — O2 proper, an element of `Arith(Rocq)`.

## 9. M6 — Inclusion / adequacy (1–2 months)

Deep-embedded arithmetic (§1.3) + the M2 Stage B nat package. A logical
relation between CDLE's encoded naturals and Rocq's `nat`, then:

```
Theorem adequacy : ∀ φ : form,   (∃ t, ⊢ t : φ̂)  →  ⟦φ⟧ℕ.
```

This is O1, fully mechanized — uniform in φ because arithmetic is deeply
embedded and truth is internal.

## 10. M7 — Gödel II side, and assembly (paper, weeks)

O3 stays on paper, deliberately. Verify Gödel II's hypotheses for CDLE:
consistent (M4), effectively presented (derivation checking is decidable),
represents arithmetic and satisfies the derivability conditions (via the
derived induction package). Mechanizing Gödel II *with CDLE as object theory*
is explicitly **out of scope** (existing mechanizations — O'Connor, Kirst et
al. — target arithmetic theories; retargeting them is its own project).

Assembly — the boxed argument, with provenance labels:

```
1. ∀ φ, CDLE ⊢ φ̂ → Rocq ⊢ ⟦φ⟧ℕ          (mechanized: M3 + M6)
2. Rocq ⊢ Con(CDLE)                        (mechanized: M3 + M4 + M5)
3. CDLE ⊬ Con(CDLE)                        (paper: M7)
∴ Arith(CDLE) ⊊ Arith(Rocq)
```

## 11. Risks, ranked

1. **Model plumbing** (M3): the volume of binder/substitution lemmas around
   the fundamental theorem. Mitigation: Autosubst; keep the semantics minimal.
2. **Generic datatype elaboration** (M2 Stage C): genuinely hard; staged so
   that every other milestone survives without it.
3. **Gödel derivability conditions for CDLE** (M7): the least-certain
   obligation in the plan; paper-level but must be written carefully. Honest
   fallback if it stalls: "Rocq ⊢ Con(CDLE) and Arith(CDLE) ⊆ Arith(Rocq)" —
   still a substantial mechanized result.
4. **Autosubst version pin**: retired as a risk — the repo is pinned to Rocq 9.0,
   Autosubst's own bound, so generator and build share one switch. What remains
   is the consequence: the project cannot move to 9.1/9.2 without dropping
   Autosubst (and hand-rolling the substitution boilerplate) or waiting for an
   `rocq-autosubst-ocaml` release that lifts `rocq-core < 9.1`.
5. **Coquedille output quality** (unannotated binders, `fresh`, `delparamsTy`):
   bounded — the elaborator rejects bad input by construction (E2), with
   upstream fixes as needed.

## 12. Ground rules

- All Rocq work — including the Autosubst generator — in the `coquedille-9.0`
  switch via `opam exec --switch=coquedille-9.0 --`. The `gadt-autosubst` switch
  belongs to another project and is not used here. The older `coquedille` switch
  is the superseded 9.2 toolchain and must not be used to build this repo.
- Develop in the persistent `cq` session (M0.4); `make` via `coq_makefile` is
  the authoritative check and must be green before any commit.
- Vendored generated code under `theories/CDLE/` is never edited by hand;
  change `autosubst/cdle.sig` and regenerate.
- Spec departures go to `DIVERGENCES.md` before the code that embodies them.
- New theory files enter `_CoqProject` as they are created; elaborator golden
  tests reuse the existing layout under `tests/`.
