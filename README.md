# jensen-ladder

A Lean 4 formalization of a **reduction lattice** for the Riemann Hypothesis:
a kernel-checked web of conditional theorems that pin RH to a single,
explicitly-stated, currently-unproven analytic input — reached independently
along several routes, each carrying its own falsifier.

> **Scope warning (load-bearing — do not drop).** This repository does **not**
> prove the Riemann Hypothesis. Theorem M (proven separately, in
> [theorem-m](../theorem-m): all complex zeros of the model family Ψ_d are
> real) is a proven *input*, but **Theorem M does not prove RH by itself.**
> RH is not proven and not falsified here.

## What is formally established

Full `lake build` is green (43 modules); no `sorry`/`admit`; no added `axiom`
declarations. Within that kernel-checked discipline the repository proves
**reductions**, not RH:

- **`RHReduction`** — RH ⟺ reality of the regular Ξ zeros (the Pólya–Jensen /
  mathlib `RiemannHypothesis` bridge).
- **`ModelToXiTransfer`** — RH ⟸ (a model endpoint such as Theorem M) +
  a `FakeZeroFreeTransferRow` + the classical Jensen gate. The load-bearing
  input is the transfer row, not the wrapper.
- **`PolyaSchurTransfer`** — the transfer row realized as a Pólya–Schur
  multiplier sequence (`M ∈ Laguerre–Pólya`), with the falsifier that any
  off-`LP` Ξ kills it.
- **`SpectralFaithfulnessGap`** — reality of a self-adjoint spectrum is free;
  the open content is **faithfulness** (every zero represented in the
  spectrum). An off-axis zero ⟹ not faithful.
- **`CVSSpectralRoute`** — Connes–van Suijlekom: simple-even finite-scale
  ground states + Hurwitz convergence ⟹ RH; convergence is the open row.
- **`DeningerCarrier`** — the non-spectral geometric carrier interface:
  `hasPolarizedFaithfulDictionary ⟺ RiemannHypothesis`. It names the carrier
  and its missing-zero falsifier; it does **not** construct Deninger's
  `H*_dyn`, a flow, a determinant identity, or a positivity theorem.
- **`MorseDeningerBridge`** — `noNegativeModes ⟺ faithful dictionary ⟺ RH`.
- Genuine below-RH content: `ResolutionWall`, `StructureTheorem`, `T1Phase`,
  `T2Edge`, the `BAH1*` criticality no-go, the `CCM*` finite-rank algebra.

Every load-bearing hypothesis above is left **unproven** (no module
instantiates it), and several are proven **equivalent** to RH — so none of
them proves RH; together they form an honest map of where the single open
input sits.

## The single open input (honest statement)

The routes' hypotheses are mutually related and reduce to one object: a
**non-spectral geometric carrier** (an arithmetic `ℤ ×_{F₁} ℤ` / Deninger
`H*_dyn` / Connes–Consani arithmetic site / Borger Λ-ring with Witt `ψ_p`
Frobenii) delivering a Hodge-index-positive intersection form / a faithful
zero dictionary. A recorded research synthesis (the *moment-problem
invariant*, `../docs/rh/what_if_rabbit_holes_20260614.md`) argues why this is
forced: "realize ζ's zeros as a spectrum/measure" is, by the Hamburger moment
problem, identical to "a Hankel/intersection positivity," which is RH — so no
spectral/positivity route is non-circular, and the only non-circular crossing
is the geometric carrier, exactly as in Weil's function-field proof (Hodge
index on `C×C`). That carrier is unconstructed; building it is the open
problem.

## Verification

```sh
cd formal && lake build                          # green, 43 modules
# confirm axiom profile (expect: [propext, Classical.choice, Quot.sound]):
#   echo 'import JensenLadder' > /tmp/ax.lean ; ...; #print axioms <endpoint>
rg -n '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' formal/JensenLadder   # none
```

License: MIT.
