import Mathlib

/-!
# The two Frobenius ruling axes of the self-product form a hyperbolic plane (T5 first stone)

Stage T5 of `docs/plans/program_T3_T5_self_product_construction_20260617.md` requires the self-product
`Spec ℤ ×_{F₁} Spec ℤ` with **two Frobenius axes** and an intersection form of Hodge-index signature
`(1, ρ−1)`. The two axes are the two **ruling families** of the surface (the fibers of the two
projections `Spec ℤ ×_{F₁} Spec ℤ → Spec ℤ`); each ruling class is **isotropic** (`f² = 0`, a fiber has
zero self-intersection) and they meet in one point (`f₁·f₂ = 1`).

This file formalizes the RH-free linear-algebra core: two isotropic vectors span a **hyperbolic plane**
(`Q(a•f₁+b•f₂) = a·b·polar(f₁,f₂)`, signature `(1,1)`), and `ℓ = f₁+f₂` is the diagonal **ample** class
(`Q ℓ = polar(f₁,f₂)`). Together with `JensenLadder.hodge_index_ineq` (negative-definite primitive part
⟹ Hodge-index signature), this is the surface structure of T5: a hyperbolic `(1,1)` from the two
Frobenius rulings, plus a negative-definite primitive part — signature `(1, ρ−1)`. RH-free; the
positivity of the *primitive* part (the no-margin / Weil positivity) is the open RH-equivalent core,
not addressed here.
-/

open QuadraticMap

namespace JensenLadder

/-- **Two isotropic (ruling) axes span a hyperbolic plane.** For isotropic `f₁, f₂`
(`Q f₁ = Q f₂ = 0`), `Q(a•f₁ + b•f₂) = a·b·(polar Q f₁ f₂)` — the hyperbolic form on their span
(signature `(1,1)` when `polar Q f₁ f₂ ≠ 0`). The T5 two-Frobenius-axis structure of the self-product. -/
theorem hyperbolic_plane_of_isotropic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f₁ f₂ : V) (h₁ : Q f₁ = 0) (h₂ : Q f₂ = 0) (a b : ℝ) :
    Q (a • f₁ + b • f₂) = a * b * QuadraticMap.polar Q f₁ f₂ := by
  have hpolar : Q (a • f₁ + b • f₂)
      = Q (a • f₁) + Q (b • f₂) + QuadraticMap.polar Q (a • f₁) (b • f₂) := by
    rw [QuadraticMap.polar]; ring
  rw [hpolar, QuadraticMap.map_smul, QuadraticMap.map_smul, h₁, h₂,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
  ring

/-- **The diagonal ample class from two rulings.** `ℓ = f₁ + f₂` has `Q ℓ = polar Q f₁ f₂`, so it is
ample (`Q ℓ > 0`) exactly when the two ruling axes meet positively (`polar Q f₁ f₂ > 0`). This is the
ample class feeding `hodge_index_ineq`. -/
theorem map_add_isotropic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f₁ f₂ : V) (h₁ : Q f₁ = 0) (h₂ : Q f₂ = 0) :
    Q (f₁ + f₂) = QuadraticMap.polar Q f₁ f₂ := by
  have := hyperbolic_plane_of_isotropic Q f₁ f₂ h₁ h₂ 1 1
  simpa using this

end JensenLadder
