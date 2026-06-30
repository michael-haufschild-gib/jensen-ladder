import Mathlib

/-!
# Lefschetz primitive decomposition by an ample class (T5 Gram backbone)

Stage T5 of `docs/plans/program_T3_T5_self_product_construction_20260617.md` builds the self-product
surface whose intersection form has Hodge-index signature `(1, ρ−1)`. The two theorems already in the
atlas — `JensenLadder.hyperbolic_plane_of_isotropic` (the two Frobenius ruling axes give a hyperbolic
`(1,1)`) and `JensenLadder.hodge_index_ineq` (`4·Qℓ·Qv ≤ polar²` from a negative primitive part) — both
rest on one piece of pure linear algebra that this file isolates and proves: the **Gram split of an
arbitrary class by an ample class**.

For an ample class `ℓ` and the scalar `c` selected by `polar Q ℓ v = 2·c·(Q ℓ)` (i.e. `c = (ℓ·v)/(2 ℓ²)`),
the **primitive part** `w = v − c•ℓ` is `Q`-orthogonal to `ℓ` and the self-intersection splits additively:

  `polar Q ℓ w = 0`   and   `Q v = c²·(Q ℓ) + Q w`.

This makes the index theory transparent: a *primitive* class (`polar Q ℓ v = 0`, so `c = 0`) has
`Q v = Q w`, so negative-definiteness of `ℓ^⊥` is exactly `ℓ·v = 0 ⟹ v² ≤ 0` (the qualitative Hodge index
theorem); and with `c = polar/(2Qℓ)` the split is `Q v = (polar Q ℓ v)²/(4Qℓ) + Q w`, which under `Q w ≤ 0`
is precisely `hodge_index_ineq`. Specialized to `ℓ = f₁+f₂` (diagonal ample class of the self-product) and
`v = ` a correspondence graph, it is the algebra that turns a *signature* statement into the
correspondence/Weil eigenvalue bound.

**RH-free.** The split holds for any quadratic form (ζ or DH alike). The entire RH-equivalent content is
the sign of the primitive part `Q w ≤ 0` (negative-definiteness of `ℓ^⊥`) — the no-margin / Weil-positivity
core — which is NOT addressed here. The decomposition only shows *where* RH concentrates: a single
inequality on the primitive subspace. See `docs/rh/hawking_primitive_decomposition_T5_20260618.md`.
-/

open QuadraticMap

namespace JensenLadder

/-- **Lefschetz primitive decomposition by an ample class.** Given a quadratic form `Q`, a class `ℓ`,
a class `v`, and the scalar `c` fixed by `polar Q ℓ v = 2·c·(Q ℓ)` (so `c = (ℓ·v)/(2 ℓ²)` when `ℓ² ≠ 0`),
the primitive part `w := v − c•ℓ` is orthogonal to `ℓ` and the self-intersection splits additively:
`polar Q ℓ (v − c•ℓ) = 0` and `Q v = c²·(Q ℓ) + Q (v − c•ℓ)`. RH-free; the positivity of the primitive
part is the open Weil-positivity core, not asserted here. -/
theorem primitive_decomposition {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (ℓ v : V) (c : ℝ) (hc : polar Q ℓ v = 2 * c * Q ℓ) :
    polar Q ℓ (v - c • ℓ) = 0 ∧ Q v = c ^ 2 * Q ℓ + Q (v - c • ℓ) := by
  have hpℓℓ : polar Q ℓ ℓ = 2 * Q ℓ := by
    rw [QuadraticMap.polar_self, nsmul_eq_mul]; norm_num
  have hortho : polar Q ℓ (v - c • ℓ) = 0 := by
    rw [sub_eq_add_neg, polar_add_right, polar_neg_right, polar_smul_right, hc, hpℓℓ]
    simp only [smul_eq_mul]; ring
  refine ⟨hortho, ?_⟩
  have hsplit : v = (v - c • ℓ) + c • ℓ := by abel
  have hexp : Q v = Q (v - c • ℓ) + Q (c • ℓ) + polar Q (v - c • ℓ) (c • ℓ) := by
    conv_lhs => rw [hsplit]
    rw [QuadraticMap.polar]; ring
  have hcross : polar Q (v - c • ℓ) (c • ℓ) = 0 := by
    rw [polar_smul_right, polar_comm, hortho]; simp
  rw [hexp, hcross, QuadraticMap.map_smul]
  simp only [smul_eq_mul]; ring

end JensenLadder
