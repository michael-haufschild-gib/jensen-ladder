import Mathlib

/-!
# Concavity of the Weil-bottom in the prime-weight scaling (variational backbone)

The structural foundation of the prime-weight variational principle
(`docs/rh/hawking_prime_weight_variational_20260618.md`): the bottom eigenvalue of the CCM Weil
operator, scaled in the prime strength,
`bottom(Q_W(t)) = λ_min(W₀₂ − W_R − t·P_prime) = ⨅_x (⟨x,(W₀₂−W_R)x⟩ − t·⟨x,P_prime x⟩)`,
is **concave in t** — because it is a pointwise infimum of the affine-in-`t` Rayleigh functionals
`t ↦ ⟨x,Ax⟩ − t⟨x,Bx⟩`. Concavity ⟹ a unique maximum, which the experiments locate at the genuine
von Mangoldt strength `t=1`, with maximal value `0` (the marginal-positivity edge; that the max is
*exactly* `0` in the limit is Weil positivity = RH, and is NOT proved here).

This file formalizes the RH-free essence: the pointwise infimum of a finite family of affine
functions is concave. (Specialize `A i = ⟨xᵢ,(W₀₂−W_R)xᵢ⟩`, `B i = ⟨xᵢ,P_prime xᵢ⟩` over a finite
ε-net / eigenbasis of Rayleigh quotients.)
-/

open scoped BigOperators

namespace JensenLadder

/-- **Concavity of an infimum of affine functions** (the Weil-bottom variational backbone). For a
finite family, `t ↦ ⨅ i, (A i − t·B i)` is concave on `ℝ`. Hence `bottom(Q_W(t)) = λ_min(A − tB)`
(an inf of affine Rayleigh functionals) is concave in the prime-weight scaling `t`, so it has a
unique maximum (located experimentally at the genuine von Mangoldt strength). RH-free. -/
theorem concaveOn_iInf_affine {ι : Type*} [Fintype ι] [Nonempty ι] (A B : ι → ℝ) :
    ConcaveOn ℝ Set.univ (fun t : ℝ => ⨅ i, (A i - t * B i)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  simp only [smul_eq_mul]
  have hbddx : BddBelow (Set.range (fun i => A i - x * B i)) :=
    Set.Finite.bddBelow (Set.finite_range _)
  have hbddy : BddBelow (Set.range (fun i => A i - y * B i)) :=
    Set.Finite.bddBelow (Set.finite_range _)
  refine le_ciInf ?_
  intro i
  have hx : (⨅ j, (A j - x * B j)) ≤ A i - x * B i := ciInf_le hbddx i
  have hy : (⨅ k, (A k - y * B k)) ≤ A i - y * B i := ciInf_le hbddy i
  have h1 : p * (⨅ j, (A j - x * B j)) ≤ p * (A i - x * B i) := mul_le_mul_of_nonneg_left hx hp
  have h2 : q * (⨅ k, (A k - y * B k)) ≤ q * (A i - y * B i) := mul_le_mul_of_nonneg_left hy hq
  have e : p * (A i - x * B i) + q * (A i - y * B i) = A i - (p * x + q * y) * B i := by
    linear_combination (A i) * hpq
  linarith [h1, h2, e]

end JensenLadder
