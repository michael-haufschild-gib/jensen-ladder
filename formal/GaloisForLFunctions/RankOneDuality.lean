import GaloisForLFunctions.Core

/-!
# Rank-one dual multiplier algebra

This file formalizes the finite algebraic core used by the orthogonality
meta-theorem: in a rank-one multiplier system, the dual multiplier is the
inverse multiplier, and a self-dual multiplier must have square one.

No Tannakian category, functional-equation polarization, Weil positivity, or RH
statement is formalized here.
-/

namespace GaloisForLFunctions

section

variable {G : Type*} [Group G]

/-- The dual multiplier of a rank-one multiplier is its inverse. -/
def rankOneDualMultiplier (g : G) : G := g⁻¹

/-- The original and dual rank-one multipliers pair to the identity. -/
theorem rankOneDualMultiplier_mul (g : G) : g * rankOneDualMultiplier g = 1 := by
  simp [rankOneDualMultiplier]

/-- The dual and original rank-one multipliers pair to the identity in the
opposite order as well. -/
theorem rankOneDualMultiplier_mul_left (g : G) : rankOneDualMultiplier g * g = 1 := by
  simp [rankOneDualMultiplier]

/-- A rank-one multiplier is equal to its dual exactly when it has square one. -/
theorem rankOne_selfDualMultiplier_iff_sq_eq_one (g : G) :
    rankOneDualMultiplier g = g ↔ g ^ 2 = 1 := by
  constructor
  · intro h
    have hinv : g⁻¹ = g := by simpa [rankOneDualMultiplier] using h
    calc
      g ^ 2 = g * g := by rw [pow_two]
      _ = g⁻¹ * g := by rw [hinv]
      _ = 1 := by simp
  · intro h
    have hmul : g * g = 1 := by simpa [pow_two] using h
    calc
      rankOneDualMultiplier g = g⁻¹ := rfl
      _ = g⁻¹ * 1 := by simp
      _ = g⁻¹ * (g * g) := by rw [hmul]
      _ = g := by simp

/-- A multiplier whose square is not one cannot be self-dual. -/
theorem rankOne_noSelfDualMultiplier_of_sq_ne_one (g : G) (h : g ^ 2 ≠ 1) :
    rankOneDualMultiplier g ≠ g := by
  intro hself
  exact h ((rankOne_selfDualMultiplier_iff_sq_eq_one g).mp hself)

end

end GaloisForLFunctions
