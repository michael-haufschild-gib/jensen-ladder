import Mathlib

/-!
# The Hodge-index inequality (Lorentzian / "one positive direction")

The finite-dimensional core of Stage 0/2 of the T3/T5 carrier-construction sub-program
(`docs/plans/program_T3_T5_self_product_construction_20260617.md`,
`docs/rh/hawking_T3T5_stage0_2_inertia_core_20260617.md`).

For a real quadratic form `Q` with an *ample* vector `ℓ` (`Q ℓ > 0`) that is *negative-semidefinite on
its own polar-orthogonal complement* (`polar Q ℓ w = 0 → Q w ≤ 0`), the reverse Cauchy–Schwarz
inequality holds:

  `4 · (Q ℓ) · (Q v) ≤ (polar Q ℓ v)^2`   for all `v`.

This is the Hodge-index / Lorentzian-signature statement at the level of the form: any `v` with
`Q v > 0` must satisfy `polar Q ℓ v ≠ 0` (it is *not* primitive), i.e. the form has at most one
positive direction (the ample line). It is RH-free pure linear algebra; it makes precise, and
machine-checks, the "HR ⟺ inertia (1, n−1)" reduction (Prop 1/3 of the inertia-core worklog) in its
sharp inequality form, with no subspace-dimension or `sigPos` API required.

Companion: `MomentPositivity.scForm_sigNeg_eq_inside` (the dual *count* `sigNeg = #inside`); together
they are the two faces (signature / definiteness) of the single off-line-zero invariant `κ₋`.
-/

open QuadraticMap

namespace JensenLadder

/-- **Hodge-index inequality** (reverse Cauchy–Schwarz = Lorentzian / "one positive direction").
If `Q ℓ > 0` (ample) and `Q ≤ 0` on the polar-orthogonal complement of `ℓ`, then
`4 (Q ℓ)(Q v) ≤ (polar Q ℓ v)^2` for all `v`. Hence any `v` with `Q v > 0` has `polar Q ℓ v ≠ 0`
(not primitive): the form has at most one positive direction. -/
theorem hodge_index_ineq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (ℓ : V) (hℓ : 0 < Q ℓ)
    (hneg : ∀ w, QuadraticMap.polar Q ℓ w = 0 → Q w ≤ 0) (v : V) :
    4 * Q ℓ * Q v ≤ (QuadraticMap.polar Q ℓ v) ^ 2 := by
  have h2 : (2 * Q ℓ) ≠ 0 := ne_of_gt (by linarith)
  set c : ℝ := QuadraticMap.polar Q ℓ v / (2 * Q ℓ) with hc
  set w : V := v - c • ℓ with hw
  have hpℓℓ : QuadraticMap.polar Q ℓ ℓ = 2 * Q ℓ := by
    rw [QuadraticMap.polar_self]; ring
  have hpw : QuadraticMap.polar Q ℓ w = 0 := by
    have hstep : QuadraticMap.polar Q ℓ w
        = QuadraticMap.polar Q ℓ v - c * QuadraticMap.polar Q ℓ ℓ := by
      rw [hw, sub_eq_add_neg, ← neg_smul, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_right]
      ring
    rw [hstep, hpℓℓ, hc]; field_simp; ring
  have hQv : Q v = Q w + c ^ 2 * Q ℓ := by
    have hvw : v = w + c • ℓ := by rw [hw]; abel
    rw [hvw]
    have hexp : Q (w + c • ℓ) = Q w + Q (c • ℓ) + QuadraticMap.polar Q w (c • ℓ) := by
      rw [QuadraticMap.polar]; ring
    have hpwl : QuadraticMap.polar Q w (c • ℓ) = 0 := by
      rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hpw, smul_zero]
    have hsm : Q (c • ℓ) = c ^ 2 * Q ℓ := by
      rw [QuadraticMap.map_smul, smul_eq_mul]; ring
    rw [hexp, hpwl, hsm]; ring
  have hQw : Q w ≤ 0 := hneg w hpw
  have hpv : QuadraticMap.polar Q ℓ v = c * (2 * Q ℓ) := by rw [hc]; field_simp
  have key : (QuadraticMap.polar Q ℓ v) ^ 2 - 4 * Q ℓ * Q v = - (4 * Q ℓ * Q w) := by
    rw [hpv, hQv]; ring
  nlinarith [key, mul_nonneg (le_of_lt hℓ) (neg_nonneg.mpr hQw)]

/-- Corollary (contrapositive, the "one positive direction" reading): if `ℓ` is ample and `Q ≤ 0`
on `ℓ`'s polar-orthogonal complement, then every `v` with `Q v > 0` is non-primitive
(`polar Q ℓ v ≠ 0`). -/
theorem pos_not_primitive {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (ℓ : V) (hℓ : 0 < Q ℓ)
    (hneg : ∀ w, QuadraticMap.polar Q ℓ w = 0 → Q w ≤ 0) (v : V) (hv : 0 < Q v) :
    QuadraticMap.polar Q ℓ v ≠ 0 := by
  intro h
  have := hodge_index_ineq Q ℓ hℓ hneg v
  rw [h] at this
  nlinarith [mul_pos hℓ hv]

end JensenLadder
