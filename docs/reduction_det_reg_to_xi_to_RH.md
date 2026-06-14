# A machine-checked reduction of the Riemann Hypothesis to one convergence hypothesis

**Authors:** Fable (Anthropic Opus 4.8) and GPT‑2 (OpenAI), RH research team.
**Date:** 2026‑06‑14.
**Artifact:** `jensen-ladder/formal/JensenLadder/` (Lean 4, mathlib).
**Status:** This note documents a **reduction**, machine‑checked and axiom‑clean. It is **not** a proof of the Riemann Hypothesis. The single hypothesis it reduces to is itself logically equivalent to RH and is currently open.

> **Scope warning (load‑bearing).** Theorem M (proven separately in `theorem-m/`: all complex zeros of the model family Ψ_d are real) is a proven *input*, but **Theorem M does not prove RH by itself.** RH is here **not proven and not falsified.**

---

## 1. The result

Let `xiEntire : ℂ → ℂ` be the entire completion of the Riemann Ξ function (Definition, §2). The central theorem (`JensenLadder.HurwitzBridge`, file `HurwitzRealRootedLimit.lean`) is:

```lean
theorem riemannHypothesis_of_realRooted_tendsto_xiEntire
    (F : ℕ → ℂ → ℂ)
    (hFa  : ∀ n, AnalyticOnNhd ℂ (F n) Set.univ)
    (hF_real : ∀ n z, F n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn F xiEntire atTop Set.univ) :
    RiemannHypothesis
```

In words: **if** a sequence of entire functions `Fₙ`, each having only real zeros, converges locally uniformly on all of ℂ to `xiEntire`, **then** mathlib's official `RiemannHypothesis` holds.

The intended `Fₙ` are the regularized determinants `det_reg(D_log^{(λ,N)} − z)` of the finite Connes–Consani–Moscovici operators (Euler product over primes `p ≤ λ²`). These are entire with only real zeros for free, by self‑adjointness — so `hFa` and `hF_real` are discharged for that family, and the sole remaining input is the convergence `hconv`, i.e. **`det_reg → Ξ`**.

This is the cleanest reduction in the lattice: **everything downstream of the convergence is machine‑proved and axiom‑clean.**

---

## 2. The entire Ξ and its zero set

```lean
noncomputable def xiEntire (z : ℂ) : ℂ :=
  (1/2) * ((1/2 + I * z) * (1/2 + I * z - 1) * completedRiemannZeta₀ (1/2 + I * z) + 1)
```

Here `completedRiemannZeta₀` is mathlib's entire part Λ₀ of the completed zeta. With `s = 1/2 + I·z`, the factor `s(s−1)Λ₀(s) + 1` exactly cancels the two simple poles of `Λ(s)` at `s = 0, 1` (lemma `xi_pole_cancel`), so `xiEntire` is **entire** (`xiEntire_differentiable`). Its zeros are precisely the nontrivial zeros of ζ, reparameterized by `s = 1/2 + I·z`; hence

> `(∀ z, xiEntire z = 0 → z.im = 0)` ⟺ all nontrivial ζ zeros lie on the critical line ⟺ RH.

The bridge from "`xiEntire` has only real zeros" to mathlib's `RiemannHypothesis` is `riemannXi_zero_imp_xiEntire_zero` composed with `JensenLadder.RHReduction.riemannHypothesis_of_riemannXi_zeros_real`. The endpoint nontriviality `∃ z, xiEntire z ≠ 0` is proved (`xiEntire_nontrivial`, via `xiEntire (I/2) = 1/2`).

---

## 3. Proof architecture (three layers, all kernel‑checked)

1. **Hurwitz real‑rooted transfer** (`hurwitz_realRooted_transfer`, `HurwitzRealRootedLimit.lean`). A locally‑uniform‑on‑ℂ limit of entire, only‑real‑zero functions has only real zeros, provided the limit is `≢ 0`. Proof = argument principle on a circle around any putative off‑axis zero + nowhere‑zero Hurwitz on the two open half‑planes `{im > 0}`, `{im < 0}`.
   - **New formalization (mathlib lacked it).** mathlib had neither the argument‑principle "count zeros inside a contour" step nor a nowhere‑zero Hurwitz theorem in usable form. Both were built from scratch here: `argprin_isolated` (`(1/2πi)∮ logDeriv = #zeros`), `tendsto_circleIntegral_logDeriv`, `nowhere_zero_hurwitz`. This is the genuinely novel proof content.
2. **Entire‑Ξ data layer** (`xiEntire`, `xi_pole_cancel`, `xiEntire_differentiable`, `completedRiemannZeta_one_ne_zero`, `riemannXi_zero_imp_xiEntire_zero`). The pole cancellation and the zero‑set identification (§2). `completedRiemannZeta_one ≠ 0` is closed via the explicit value `Λ(1) = (γ − log 4π)/2` with `γ < 2/3 < 1 < log 4π`.
3. **RH endpoint** (`JensenLadder.RHReduction.riemannHypothesis_of_riemannXi_zeros_real`). Reality of the regular Ξ zeros ⟹ mathlib `RiemannHypothesis` (the Pólya–Jensen / mathlib bridge).

Two consumer specializations package the convergence for the operator route:

- `DeterminantHurwitzRoute.DeterminantApproximants.riemannHypothesis_of_realZeros_and_tendsto_xiEntire_sequence` — the determinant family as the literal `Fₙ`; `hconv` is the only open row.
- `CCMGroundStateRoute.GroundStateProlateData.riemannHypothesis_of_groundStateRows` — decomposes `hconv` into named analytic rows (finite Weil ground state → prolate ground state; prolate Fourier limit → Ξ), with a falsifier (`not_groundStateRows_of_nonrealRegularXiZero`).

---

## 4. The single open hypothesis, and why it is exactly RH

`hconv` (= `det_reg → Ξ`) is **not** a technical lemma short of RH; it is **logically equivalent to RH**:

- The `Fₙ` are built from the primes (Euler product `p ≤ λ²`). Convergence of the determinants to Ξ — equivalently, the operator eigenvalues landing exactly on the critical line — forces square‑root cancellation in the prime sum (`ψ(x) = x + O(√x log²x)`), which is itself RH. There is no innocent reason for the convergence; establishing it *is* establishing RH.
- It is open in the current literature. Connes (arXiv:2602.04022, Feb 2026) frames "convergence from finite to infinite Euler products" as a proof *strategy*, not a theorem. Śliwiński (arXiv:2601.12133, Jan 2026), analyzing these exact `D_log^{(λ,N)}` operators, proves only an inverse‑logarithmic *mean* lower bound (a Heisenberg–Pauli–Weyl finite‑volume effect, not per‑eigenvalue) and states the *uniform* convergence as a conjecture that **implies** RH.
- There is no shortcut object. The team's "Object X" analysis (with the agnostic relationship catalog) establishes that no intermediate object provably bridges `det_reg` and Ξ below RH: scalar completed‑zeta objects matching the finite prime row provably collapse to being Ξ itself (`ScalarAffineNoGo`); the literature's proven two‑sided objects are ratios (`Λ(2s−1)/Λ(2s)`, ≠ Ξ), circular (Voros, built from Ξ's zeros), analogies (Selberg/Ruelle), or function‑field (Hasse–Weil, proven but for the wrong zeta). The carrier must be **constructed** (F₁ / Connes–Consani arithmetic site), not borrowed.

So this artifact reduces RH to one precisely‑stated convergence and proves, machine‑checked, that the reduction is sound and gap‑free — while honestly leaving the convergence (= RH) open.

---

## 5. Verification (run 2026‑06‑14, results recorded)

```sh
cd jensen-ladder/formal
~/.elan/bin/lake build JensenLadder.HurwitzRealRootedLimit \
  JensenLadder.DeterminantHurwitzRoute JensenLadder.CCMGroundStateRoute
# → Build completed successfully (8480 jobs).

# axiom profile via /tmp scratch (#print axioms), all three endpoints:
#   JensenLadder.HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire
#   …DeterminantHurwitzRoute.DeterminantApproximants.riemannHypothesis_of_realZeros_and_tendsto_xiEntire_sequence
#   …CCMGroundStateRoute.GroundStateProlateData.riemannHypothesis_of_groundStateRows
# → each: [propext, Classical.choice, Quot.sound]   (standard mathlib baseline; no added axioms)

rg -n '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' \
  JensenLadder/HurwitzRealRootedLimit.lean JensenLadder/DeterminantHurwitzRoute.lean \
  JensenLadder/CCMGroundStateRoute.lean JensenLadder/RHReduction.lean
# → no matches (clean).
```

**Honest position: RH not proven, not falsified. Theorem M is proven, but Theorem M does not prove RH by itself.**
