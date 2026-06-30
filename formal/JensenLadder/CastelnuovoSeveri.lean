import JensenLadder.SelfProductRulings

/-!
# Castelnuovo–Severi inequality on the self-product (the Weil-bound mechanism, RH-free)

Stage T5 of `docs/plans/program_T3_T5_self_product_construction_20260617.md`. On the self-product surface
`Spec ℤ ×_{F₁} Spec ℤ` the two Frobenius rulings `f₁, f₂` are isotropic and meet (cf.
`JensenLadder.hyperbolic_plane_of_isotropic`). A correspondence-type class decomposes as
`Γ = a•f₂ + b•f₁ + P`, where `(b, a)` are its bidegrees against the two rulings and `P` is the primitive
part (orthogonal to both rulings, hence to the diagonal ample class `ℓ = f₁+f₂`).

This file proves the **Castelnuovo–Severi identity and inequality**:

  `Q Γ = a·b·(polar Q f₁ f₂) + Q P`        (identity, pure bilinear algebra), and
  `Q Γ ≤ a·b·(polar Q f₁ f₂)`              (inequality, under `Q P ≤ 0`).

With the classical meeting number `polar Q f₁ f₂ = 2` this is `Γ² ≤ 2ab` — the inequality that, applied to
the graph of Frobenius in Weil's proof, yields `|eigenvalue| = √q`, i.e. **RH for curves**. It is the
algebraic mechanism by which a Hodge-index *signature* statement becomes an *eigenvalue/zero-location*
statement.

**RH-free / honest boundary.** The identity is pure bilinear algebra. The inequality's hypothesis
`Q P ≤ 0` (negative-definiteness of the primitive lattice = the Hodge-index signature) is the open
RH-equivalent core; it is taken as a *hypothesis*, not proved. This file therefore records the *mechanism*
(`signature ⟹ bound`), not RH. It sits alongside `JensenLadder.PrimitiveHodgeWeilEngine`, whose
`Engine.primitive_nonpos` field is the same open `Q P ≤ 0` assumption isolated abstractly; here it is the
explicit geometric/correspondence form of the same handoff, built on `primitive_decomposition`'s Gram split.
-/

open QuadraticMap

namespace JensenLadder

/-- **Castelnuovo–Severi identity.** A correspondence-type class `Γ = a•f₂ + b•f₁ + P` on the
self-product (rulings `f₁,f₂` isotropic; primitive part `P` orthogonal to both) has self-intersection
`Q Γ = a·b·(polar Q f₁ f₂) + Q P`. Pure bilinear algebra (RH-free). -/
theorem castelnuovo_severi {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f₁ f₂ P : V) (a b : ℝ)
    (h₁ : Q f₁ = 0) (h₂ : Q f₂ = 0)
    (hP₁ : polar Q f₁ P = 0) (hP₂ : polar Q f₂ P = 0) :
    Q (a • f₂ + b • f₁ + P) = a * b * polar Q f₁ f₂ + Q P := by
  have hX : Q (a • f₂ + b • f₁) = a * b * polar Q f₁ f₂ := by
    rw [hyperbolic_plane_of_isotropic Q f₂ f₁ h₂ h₁ a b, polar_comm]
  have hcross : polar Q (a • f₂ + b • f₁) P = 0 := by
    rw [polar_add_left, polar_smul_left, polar_smul_left, hP₁, hP₂]
    simp
  have hexp : Q (a • f₂ + b • f₁ + P)
      = Q (a • f₂ + b • f₁) + Q P + polar Q (a • f₂ + b • f₁) P := by
    rw [QuadraticMap.polar]; ring
  rw [hexp, hX, hcross]; ring

/-- **Castelnuovo–Severi inequality (abstract Hodge-index form).** If in addition the primitive part is
non-positive (`Q P ≤ 0` — the negative-definiteness of the primitive lattice / Hodge-index signature),
then `Q Γ ≤ a·b·(polar Q f₁ f₂)`. With `polar Q f₁ f₂ = 2` this is the classical `Γ² ≤ 2ab`, the inequality
that in Weil's proof yields RH for curves. The hypothesis `Q P ≤ 0` is the open RH-equivalent core (the
same assumption as `PrimitiveHodgeWeilEngine.Engine.primitive_nonpos`); NOT proved here. -/
theorem castelnuovo_severi_ineq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f₁ f₂ P : V) (a b : ℝ)
    (h₁ : Q f₁ = 0) (h₂ : Q f₂ = 0)
    (hP₁ : polar Q f₁ P = 0) (hP₂ : polar Q f₂ P = 0) (hPneg : Q P ≤ 0) :
    Q (a • f₂ + b • f₁ + P) ≤ a * b * polar Q f₁ f₂ := by
  rw [castelnuovo_severi Q f₁ f₂ P a b h₁ h₂ hP₁ hP₂]; linarith

end JensenLadder
