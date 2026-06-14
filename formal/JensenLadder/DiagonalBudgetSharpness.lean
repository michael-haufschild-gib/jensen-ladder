import JensenLadder.PrimeDominationBabyCarrier
import Mathlib.Tactic

/-!
# Diagonal budget sharpness

This module proves that the absolute diagonal budget used in the finite
domination reductions is sharp for a uniform symmetric two-mode completion.

For the block

```text
  a*x^2 + 2*c*x*y + a*y^2,
```

nonnegativity for all real `x,y` is equivalent to `|c| <= a`.  Thus the local
budget `|c|` per endpoint is not merely sufficient; it is necessary for this
rank-two symmetric certificate.

This does not prove RH or the zeta archimedean domination inequality.  It
sharpens the finite algebra that any carrier-side global domination theorem
would plug into.  Theorem M is proven, but Theorem M does not prove RH by
itself.

Evidence class: formal/certificate artifact; proved lemma.
-/

namespace JensenLadder
namespace DiagonalBudgetSharpness

/-- Symmetric two-mode completion with endpoint diagonal coefficient `a`. -/
def symmetricCompletedBlock (a c x y : ℝ) : ℝ :=
  a * x ^ 2 + 2 * c * x * y + a * y ^ 2

/-- The square/eigenmode decomposition of the same block. -/
noncomputable def squareDecomposition (a c x y : ℝ) : ℝ :=
  ((a + c) / 2) * (x + y) ^ 2 + ((a - c) / 2) * (x - y) ^ 2

/-- The symmetric completed block equals its square/eigenmode decomposition. -/
theorem symmetricCompletedBlock_eq_squareDecomposition
    (a c x y : ℝ) :
    symmetricCompletedBlock a c x y = squareDecomposition a c x y := by
  unfold symmetricCompletedBlock squareDecomposition
  ring

/--
If the diagonal coefficient dominates the absolute coupling, the symmetric
completed block is nonnegative.
-/
theorem symmetricCompletedBlock_nonnegative_of_abs_coupling_le_diagonal
    {a c x y : ℝ}
    (h : |c| <= a) :
    0 <= symmetricCompletedBlock a c x y := by
  have hc := abs_le.mp h
  have hplus : 0 <= a + c := by
    linarith
  have hminus : 0 <= a - c := by
    linarith
  rw [symmetricCompletedBlock_eq_squareDecomposition]
  unfold squareDecomposition
  positivity

/--
If the symmetric completed block is nonnegative for all modes, the diagonal
coefficient must dominate the absolute coupling.
-/
theorem abs_coupling_le_diagonal_of_symmetricCompletedBlock_nonnegative
    {a c : ℝ}
    (h : ∀ x y : ℝ, 0 <= symmetricCompletedBlock a c x y) :
    |c| <= a := by
  have hsame := h 1 1
  have hopp := h 1 (-1)
  unfold symmetricCompletedBlock at hsame hopp
  have hlo : -a <= c := by
    nlinarith
  have hhi : c <= a := by
    nlinarith
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- The exact sharpness criterion for symmetric endpoint diagonal completion. -/
theorem symmetricCompletedBlock_nonnegative_iff_abs_coupling_le_diagonal
    (a c : ℝ) :
    (∀ x y : ℝ, 0 <= symmetricCompletedBlock a c x y) ↔ |c| <= a := by
  constructor
  · exact abs_coupling_le_diagonal_of_symmetricCompletedBlock_nonnegative
  · intro h x y
    exact symmetricCompletedBlock_nonnegative_of_abs_coupling_le_diagonal h

/--
If the diagonal coefficient is below the absolute coupling, some two-mode input
makes the completed block negative.
-/
theorem exists_negative_of_diagonal_lt_abs_coupling
    {a c : ℝ}
    (h : a < |c|) :
    ∃ x y : ℝ, symmetricCompletedBlock a c x y < 0 := by
  by_cases hc : 0 <= c
  · have hlt : a < c := by
      rwa [abs_of_nonneg hc] at h
    refine ⟨1, -1, ?_⟩
    unfold symmetricCompletedBlock
    nlinarith
  · have hcneg : c < 0 := lt_of_not_ge hc
    have hlt : a < -c := by
      rwa [abs_of_neg hcneg] at h
    refine ⟨1, 1, ?_⟩
    unfold symmetricCompletedBlock
    nlinarith

end DiagonalBudgetSharpness
end JensenLadder
