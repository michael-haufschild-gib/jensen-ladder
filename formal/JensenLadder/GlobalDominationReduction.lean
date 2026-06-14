import JensenLadder.PrimeDominationBabyCarrier
import Mathlib.Tactic

/-!
# Global missing-diagonal domination reduction

This module isolates the finite algebra behind the sharpened carrier prompt.

The prime/off-diagonal row is modeled by arbitrary signed edge couplings
`c_e`.  Its missing diagonal budget is the sum of `|c_e|` on the two endpoint
squares.  If an external diagonal functional `arch` dominates that missing
diagonal budget for a test vector `v`, then the completed form

```text
  arch v + sum_e 2*c_e*v(left e)*v(right e)
```

is nonnegative.

This does not prove the zeta archimedean domination inequality.  It proves
that this inequality is exactly the remaining finite domination obligation:
once supplied by a carrier, the off-diagonal row is controlled without any
hypothesis about zeta zeros.

Evidence class: formal/certificate artifact; proved lemma.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace GlobalDominationReduction

/-- A finite signed off-diagonal row over an abstract edge set. -/
structure SignedEdgeAssembly (Vertex Edge : Type*) where
  left : Edge -> Vertex
  right : Edge -> Vertex
  coupling : Edge -> ℝ

namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/-- The missing diagonal budget needed to complete all signed edge couplings. -/
def missingDiagonalBudget (A : SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    PrimeDominationBabyCarrier.weightedDiagonalBudget
      (A.coupling e) (v (A.left e)) (v (A.right e))

/-- The signed off-diagonal row. -/
def offDiagonalRow (A : SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, 2 * A.coupling e * v (A.left e) * v (A.right e)

/-- The finite form after adding an external archimedean/pole diagonal functional. -/
def completedByArch (A : SignedEdgeAssembly Vertex Edge)
    (arch : (Vertex -> ℝ) -> ℝ) (v : Vertex -> ℝ) : ℝ :=
  arch v + A.offDiagonalRow v

omit [Fintype Edge] in
/--
One signed edge is bounded below by the negative of its missing diagonal
budget.
-/
theorem edge_offDiagonal_ge_neg_missingBudget
    (A : SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    - PrimeDominationBabyCarrier.weightedDiagonalBudget
        (A.coupling e) (v (A.left e)) (v (A.right e))
      <= 2 * A.coupling e * v (A.left e) * v (A.right e) := by
  have hnonneg :=
    PrimeDominationBabyCarrier.weightedCompletedBlock_nonnegative
      (A.coupling e) (v (A.left e)) (v (A.right e))
  unfold PrimeDominationBabyCarrier.weightedCompletedBlock at hnonneg
  unfold PrimeDominationBabyCarrier.weightedDiagonalBudget
  nlinarith

/-- The whole off-diagonal row is bounded below by the negative missing budget. -/
theorem offDiagonalRow_ge_neg_missingDiagonalBudget
    (A : SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    - A.missingDiagonalBudget v <= A.offDiagonalRow v := by
  unfold missingDiagonalBudget offDiagonalRow
  have hsum :
      (∑ e : Edge,
        - PrimeDominationBabyCarrier.weightedDiagonalBudget
            (A.coupling e) (v (A.left e)) (v (A.right e)))
        <= ∑ e : Edge, 2 * A.coupling e * v (A.left e) * v (A.right e) :=
    Finset.sum_le_sum (fun e _ =>
      A.edge_offDiagonal_ge_neg_missingBudget v e)
  rw [Finset.sum_neg_distrib] at hsum
  exact hsum

/--
The finite global-domination reduction.

If the external diagonal contribution dominates the missing diagonal budget for
`v`, then the completed form is nonnegative.
-/
theorem archDomination_implies_completed_nonnegative
    (A : SignedEdgeAssembly Vertex Edge)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hdom : A.missingDiagonalBudget v <= arch v) :
    0 <= A.completedByArch arch v := by
  have hoff : - A.missingDiagonalBudget v <= A.offDiagonalRow v :=
    A.offDiagonalRow_ge_neg_missingDiagonalBudget v
  unfold completedByArch
  linarith

end SignedEdgeAssembly

end GlobalDominationReduction
end JensenLadder
