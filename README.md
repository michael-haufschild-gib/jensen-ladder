# rh-formal-atlas

[![build & verify](https://github.com/michael-haufschild-gib/rh-formal-atlas/actions/workflows/build.yml/badge.svg)](https://github.com/michael-haufschild-gib/rh-formal-atlas/actions/workflows/build.yml)

A Lean 4 library that formalizes the *logical geometry* of the Riemann
Hypothesis (RH): the network of equivalent reformulations, and the structural
obstructions that any proof must respect. Everything is checked against
[mathlib](https://github.com/leanprover-community/mathlib4).

> **This repository does not prove the Riemann Hypothesis, and does not claim
> to.** It is a machine-checked *map* of the problem — what an object that
> would prove RH must look like, and which naive strategies provably cannot
> work. The one genuinely open input is named explicitly (below); it is not
> constructed here. RH is neither proven nor falsified in this repository.

## What this is (and isn't)

RH has dozens of known equivalent reformulations and a long folklore of
"why the easy routes fail." This library makes that informal geometry precise
and machine-checked, in three layers:

- **A reduction spine.** A short, unconditional bridge from mathlib's official
  `RiemannHypothesis` to a clean working endpoint — reality of the *regular*
  zeros of the completed zeta function in a symmetric variable `Ξ`.
- **An equivalence lattice.** RH is proved equivalent, in the kernel, to the
  existence of any one of several abstract *faithful carriers* (a Hodge-index
  object, an arithmetic-site object, a spectral realization, a Morse-index-zero
  condition, …). These are honest *reduction targets*: each records what an
  object would have to deliver, and each carries a *falsifier* (a single
  off-line zero refutes it). They are interfaces, not constructions — the
  library never builds the object.
- **No-go certificates.** Finite, fully proved theorems that rule out whole
  classes of naive strategy: that only the Euler product separates ζ from
  fakes (the Davenport–Heilbronn obstruction), that no finite spectrum can host
  infinitely many zeros, that one-sided prime-local positivity fails, that no
  margin/floor mechanism survives, and more.

The value here is not depth in any single equivalence — several are shallow by
design. It is that the whole map is *one* axiom-clean, mutually consistent,
kernel-checked artifact, with proved analytic content (ξ entire of order 1,
the zero-counting foundation) kept explicitly separate from abstract reduction
targets.

## If you came here from the paper

| You want | Where it is |
|---|---|
| The paper | [`docs/preprint/main.pdf`](docs/preprint/main.pdf) (LaTeX source beside it) |
| The headline reduction | [`formal/JensenLadder/RHReduction.lean`](formal/JensenLadder/RHReduction.lean) — `riemannHypothesis_iff_regular_riemannXi_zeros_real` |
| The carrier equivalence lattice | `formal/JensenLadder/{HodgeIndexCarrier, ArithmeticSiteCarrier, GeometricSquareRootCarrier, SpectralRealization, MorseCriterion, FredholmSquaredCarrier, …}.lean` |
| The no-go certificates | `formal/JensenLadder/{DHMultiplicityFakeGate, FiniteCarrierNoGo, PrimeLocalNoGo, ScatteringParityNoGo, ResolutionWall, …}.lean` |
| The full module-by-module map | [`docs/MODULE_INVENTORY.md`](docs/MODULE_INVENTORY.md) |
| The axiom + sorry check | [`scripts/check_axioms.sh`](scripts/check_axioms.sh) |
| The independent kernel re-check | [`scripts/check_nanoda.sh`](scripts/check_nanoda.sh) |

In Lean, the headline statement reads:

```lean
theorem riemannHypothesis_iff_regular_riemannXi_zeros_real :
    RiemannHypothesis ↔ (∀ z : ℂ, riemannXiRegularZero z → z.im = 0)
```

The development compiles with zero `sorry`s and no added `axiom`s; the headline
theorems depend only on the three axioms underlying all of mathlib (`propext`,
`Classical.choice`, `Quot.sound`). The exported declarations have also been
re-checked with [nanoda_lib](https://github.com/ammkrn/nanoda_lib), an
independent implementation of the Lean 4 kernel, via a
[lean4export](https://github.com/leanprover/lean4export) export. CI repeats all
of this on every push.

## Checking it yourself

You need [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager); everything else is pinned by the repository. The Nanoda re-check
additionally needs [Rust](https://www.rust-lang.org/tools/install).

```sh
cd formal
lake exe cache get           # fetch precompiled mathlib (a few minutes, no compiling)
lake build                   # build and kernel-check all 128 modules
../scripts/check_axioms.sh   # print the axiom report; fails on any deviation
../scripts/check_nanoda.sh   # re-check the export with the external kernel
```

## The one open input (honest statement)

The routes' open hypotheses are mutually related and reduce to a single object:
a **non-spectral geometric carrier** — an arithmetic `Spec ℤ ×_{F₁} Spec ℤ` /
Deninger dynamical cohomology / Connes–Consani arithmetic site — delivering a
Hodge-index-positive intersection form, equivalently a faithful zero
dictionary. That is exactly the object Weil's function-field proof has (the
Hodge index on `C × C`) and that the integers lack. It is unconstructed;
building it is the open problem. This library names it and its falsifier; it
does not build it.

[Theorem M](https://github.com/michael-haufschild-gib/theorem-m) (proven
separately: all zeros of an explicit Laguerre deformation `Ψ_d` are real) is a
proven *input* to one route, but **Theorem M does not prove RH by itself.**

## Authorship

The library was developed by two AI research agents — Claude (Anthropic) and
GPT (OpenAI) — under the direction of Michael Haufschild, 2026. We are aware
that AI-produced mathematics warrants extra skepticism; that is precisely why
everything here is machine-checked, why the kernel check is repeated with an
independent kernel implementation, and why the boundary between what is *proved*
and what is merely an *interface for an open problem* is made explicit in every
module's doc-string. No claim in this repository rests on trusting the authors.
If you find an error — in the paper, the code, or anything between — please open
an issue.

## License

MIT (see `LICENSE`). Depends on
[mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0).
