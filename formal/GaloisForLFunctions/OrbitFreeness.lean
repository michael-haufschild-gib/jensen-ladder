import GaloisForLFunctions.Core

/-!
# Freeness of the diagonal prime-torus orbit — additive corollaries (Tier A)

The canonical finite-character obstruction for the diagonal flow `t ↦ (p^{-it})_p`
on `𝕋^∞` is the `ℚ`-linear independence of `{log p}`, formalized in
`GaloisForLFunctions.linearIndependent_log_primes`.

This file adds two genuinely-additive citable forms built **on** that theorem, in the
field's own vocabulary:

* `logPrime_linearIndependent_int` — the `ℤ`-coefficient form, exported from `Core`;
* `logPrime_no_rat_relation` — the field-readable "no diagonal resonance" form: there is no
  nontrivial finite `ℚ`-relation `Σ q_p · log p = 0`.

Nothing here is conjectural: it is unique factorization in linear-independence vocabulary —
the finite additive coordinate of the field. Infinite torus closure, difference-Galois group
dimension, RH, and positivity/reality statements are not formalized in this file.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Field-readable form: **no nontrivial finite `ℚ`-resonance** among the prime logarithms.
This is the finite-character statement derived from `linearIndependent_log_primes`. -/
theorem logPrime_no_rat_relation
    (s : Finset Nat.Primes) (g : Nat.Primes → ℚ)
    (h : ∑ p ∈ s, g p • Real.log (p : ℕ) = 0) :
    ∀ p ∈ s, g p = 0 :=
  linearIndependent_iff'.mp linearIndependent_log_primes s g h

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- A prime-lane dilation `z ↦ p⁻¹ z` has no nonzero fixed point. This is the
algebraic core behind the repaired `Ш`-card statement that an equivariant torus
evaluation point would be forced to leave `ℂˣ`. -/
theorem primeDilation_fixed_eq_zero (p : Nat.Primes) {z : ℂ}
    (h : ((p : ℂ)⁻¹) * z = z) : z = 0 := by
  have hpC0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpC1 : (p : ℂ) ≠ 1 := by exact_mod_cast p.2.ne_one
  have hinv_ne_one : ((p : ℂ)⁻¹) ≠ 1 := by
    intro hinv
    have hmul := congrArg (fun w : ℂ => (p : ℂ) * w) hinv
    simp [hpC0] at hmul
    exact hpC1 hmul.symm
  have hcoef : ((p : ℂ)⁻¹ - 1) ≠ 0 := sub_ne_zero.mpr hinv_ne_one
  have hz : (((p : ℂ)⁻¹ - 1) * z = 0) := by
    calc
      (((p : ℂ)⁻¹ - 1) * z) = ((p : ℂ)⁻¹) * z - z := by ring
      _ = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp hz).resolve_left hcoef

/-- No coordinate in the algebraic torus `ℂˣ` is fixed by a prime-lane dilation. -/
theorem primeDilation_no_fixed_unit (p : Nat.Primes) (z : ℂˣ) :
    ((p : ℂ)⁻¹) * (z : ℂ) ≠ (z : ℂ) := by
  intro h
  exact z.ne_zero (primeDilation_fixed_eq_zero p h)

/-- There is no torus point fixed coordinatewise by all prime-lane dilations. -/
theorem no_primeDilation_fixed_torus_point (ξ : Nat.Primes → ℂˣ) :
    ¬ (∀ p : Nat.Primes, ((p : ℂ)⁻¹) * (ξ p : ℂ) = (ξ p : ℂ)) := by
  intro h
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact primeDilation_no_fixed_unit two (ξ two) (h two)

end

end GaloisForLFunctions
