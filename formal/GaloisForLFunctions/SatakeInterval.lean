import Mathlib

/-!
# The Sato–Tate interval / Ramanujan trace bound (Tier A)

This file formalizes the elementary Satake-level core of Sato–Tate / Ramanujan
(`automorphic-continent-rankin-selberg-ramanujan.md`): a **unitary** (tempered)
`GL₂` Satake parameter is a point `z` on the unit circle with contragredient
`z⁻¹`, and its **trace** `z + z⁻¹` is then real and lies in the **Sato–Tate
interval** `[−2, 2]` (the support of the Sato–Tate measure; equivalently
`z + z⁻¹ = 2cos θ`).

This is the elementary unit-circle computation underlying temperedness. It does
not formalize the Sato–Tate equidistribution theorem, the measure itself, or the
Ramanujan conjecture as an analytic bound on automorphic Satake parameters.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Sato–Tate trace is real.** For a unitary Satake parameter `z` (`‖z‖ = 1`),
the trace `z + z⁻¹` equals the real number `2·Re z` (`= 2cos θ`); in particular
it is real. -/
theorem satake_trace_eq_two_mul_re (z : ℂ) (h : ‖z‖ = 1) :
    z + z⁻¹ = ((2 * z.re : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj h, Complex.add_conj]

/-- The unitary Satake trace has vanishing imaginary part (it is real). -/
theorem satake_trace_im (z : ℂ) (h : ‖z‖ = 1) : (z + z⁻¹).im = 0 := by
  rw [satake_trace_eq_two_mul_re z h, Complex.ofReal_im]

/-- **The Sato–Tate interval.** For a unitary Satake parameter `z` (`‖z‖ = 1`),
the trace `z + z⁻¹` lies in `[−2, 2]` (the support of the Sato–Tate measure). -/
theorem satake_trace_re_mem_Icc (z : ℂ) (h : ‖z‖ = 1) :
    (z + z⁻¹).re ∈ Set.Icc (-2 : ℝ) 2 := by
  have h1 : z.re ≤ 1 := h ▸ Complex.re_le_norm z
  have h2 : -1 ≤ z.re := by
    have hz := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg, h] at hz
    linarith
  rw [satake_trace_eq_two_mul_re z h, Complex.ofReal_re, Set.mem_Icc]
  exact ⟨by linarith, by linarith⟩

/-- **Symᵏ temperedness (Sato–Tate bound for `Symᵏ`).** For a unitary Satake
parameter `z` (`‖z‖ = 1`), the `Symᵏ` trace `Σ_{j=0}^{k} z^{k-2j}` has norm
`≤ k+1` (the dimension of `Symᵏ`): its `k+1` eigenvalues `z^{k-2j}` all lie on
the unit circle, so the trace lies in the closed disk of radius `k+1` — the
temperedness bound for `Symᵏπ`. -/
theorem symPower_trace_norm_le (z : ℂ) (h : ‖z‖ = 1) (k : ℕ) :
    ‖∑ j ∈ Finset.range (k + 1), z ^ ((k : ℤ) - 2 * (j : ℤ))‖ ≤ (k : ℝ) + 1 := by
  calc ‖∑ j ∈ Finset.range (k + 1), z ^ ((k : ℤ) - 2 * (j : ℤ))‖
      ≤ ∑ j ∈ Finset.range (k + 1), ‖z ^ ((k : ℤ) - 2 * (j : ℤ))‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range (k + 1), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_zpow, h, one_zpow]
    _ = (k : ℝ) + 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast; ring

end

end GaloisForLFunctions
