import Mathlib

/-!
# The entire completed ξ and its zero-divisor — Riemann–von Mangoldt, step 2

Toward the Riemann–von Mangoldt zero-counting formula (see `ZeroCountingN`).  This module
introduces the **entire** completed Riemann ξ-function in the `s`-variable and equips it with the
mathlib meromorphic-**divisor** framework (the multiplicity-aware zero count that the argument
principle computes), then proves the bridge to `ζ`:

* `xiE s = ½ (s (s-1) Λ₀(s) + 1)`, `Λ₀ = completedRiemannZeta₀`, is **entire**.
* `xiE` is `MeromorphicOn ℂ` and (being entire) has a **nonnegative divisor**, so
  `MeromorphicOn.divisor xiE univ` is the well-defined multiplicity function of its zeros.
* Off the poles `{0,1}`, `xiE s = ½ s (s-1) Λ(s)` (`Λ = completedRiemannZeta`).
* **Bridge:** in the open critical strip `0 < Re s < 1`, `xiE s = 0 ↔ riemannZeta s = 0` — the zeros
  of the entire ξ there are exactly the nontrivial zeros of ζ.  This lets the (analytic)
  argument-principle count of `xiE` be transported to `N(T)` (`ZeroCountingN.N`, built on
  mathlib's `riemannZetaZeros`).

RH-agnostic and unconditional.  Does NOT prove RH; Theorem M does not prove RH by itself.
-/

namespace JensenLadder.RvMXiEntire

open Complex

/-- The entire completed Riemann ξ in the `s`-variable: `ξ_E(s) = ½(s(s-1)Λ₀(s)+1)`, where
`Λ₀ = completedRiemannZeta₀` is entire. -/
noncomputable def xiE (s : ℂ) : ℂ := (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- `ξ_E` is entire. -/
theorem xiE_differentiable : Differentiable ℂ xiE := by
  unfold xiE
  have h := differentiable_completedZeta₀
  fun_prop

/-- `ξ_E` is analytic on all of `ℂ` (entire). -/
theorem xiE_analyticOnNhd : AnalyticOnNhd ℂ xiE Set.univ :=
  xiE_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- `ξ_E` is meromorphic on `ℂ` (in fact analytic, being entire) — so its divisor is defined. -/
theorem xiE_meromorphicOn : MeromorphicOn xiE Set.univ :=
  AnalyticOnNhd.meromorphicOn xiE_analyticOnNhd

/-- Being entire (no poles), `ξ_E` has a nonnegative divisor: `MeromorphicOn.divisor xiE univ`
is the multiplicity function of its zeros, the quantity the argument principle computes. -/
theorem xiE_divisor_nonneg : 0 ≤ MeromorphicOn.divisor xiE Set.univ :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg xiE_analyticOnNhd

/-- Off the poles `{0,1}`, `ξ_E(s) = ½ s(s-1) Λ(s)` with `Λ = completedRiemannZeta`. -/
theorem xiE_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiE s = (1 / 2) * (s * (s - 1) * completedRiemannZeta s) := by
  unfold xiE
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- **Bridge to ζ.** In the open critical strip `0 < Re s < 1`, the zeros of the entire `ξ_E` are
exactly the nontrivial zeros of `ζ`. -/
theorem xiE_zero_iff_zeta_zero (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    xiE s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs0
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  rw [xiE_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0, div_eq_zero_iff]
  constructor
  · intro h
    refine Or.inl ?_
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h3 | h3
        · exact absurd h3 h0
        · exact absurd h3 hsub
      · exact h''
  · rintro (h | h)
    · rw [h]; ring
    · exact absurd h hG

/-- **Bridge to `riemannZetaZeros`** (RvM-1's basis): in the open critical strip, `s` is a zero of
the entire `ξ_E` iff `s ∈ riemannZetaZeros`. This transports the (analytic) argument-principle count
of `ξ_E` onto `ZeroCountingN.N`. -/
theorem xiE_zero_iff_mem_zetaZeros (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    xiE s = 0 ↔ s ∈ riemannZetaZeros := by
  rw [mem_riemannZetaZeros]
  exact xiE_zero_iff_zeta_zero s hs0 hs1

end JensenLadder.RvMXiEntire
