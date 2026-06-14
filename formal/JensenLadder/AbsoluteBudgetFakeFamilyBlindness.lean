import JensenLadder.RowDiagonalDominationCarrier
import JensenLadder.SchurStarDominationCarrier
import Mathlib.Tactic

/-!
# Absolute-budget fake-family blindness

This module records a small carrier-area no-go: domination certificates that
only see absolute coefficient budgets are invariant under unit sign twists of
the finite-prime row.

For the row-sum certificate, replacing every coupling `c_e` by
`twist e * c_e` with `|twist e| = 1` leaves the incident budget unchanged.  For
the Schur-star certificate, replacing every response coefficient by
`twist e * response e` leaves the response budget unchanged.  Therefore these
certificates prove positivity for every such fake replay, not just for the
zeta prime-power row.

This does not refute the carrier program.  It isolates a necessary condition:
the missing zeta carrier must use arithmetic structure beyond absolute
budgets, such as a named Euler-product/multiplicativity row.  Theorem M is
proven, but Theorem M does not prove RH by itself.

Evidence class: formal/certificate artifact; dead-end elimination.
-/

namespace JensenLadder
namespace AbsoluteBudgetFakeFamilyBlindness

namespace RowAssembly

open RowDiagonalDominationCarrier

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]

/-- Retwist every signed edge coupling by a scalar sign/phase. -/
def retwist (A : RowDiagonalDominationCarrier.RowAssembly Vertex Edge)
    (twist : Edge -> ℝ) : RowDiagonalDominationCarrier.RowAssembly Vertex Edge where
  left := A.left
  right := A.right
  coupling := fun e => twist e * A.coupling e
  diagonal := A.diagonal

omit [Fintype Vertex] in
/-- Unit twists do not change the absolute incident row budget. -/
theorem incidentBudget_retwist_of_abs_twist_eq_one
    (A : RowDiagonalDominationCarrier.RowAssembly Vertex Edge)
    (twist : Edge -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (i : Vertex) :
    (retwist A twist).incidentBudget i = A.incidentBudget i := by
  unfold retwist RowDiagonalDominationCarrier.RowAssembly.incidentBudget
  apply Finset.sum_congr rfl
  intro e _he
  simp [abs_mul, htwist e]

/--
Row domination by absolute budgets is fake-family blind: the same diagonal
certificate proves nonnegativity for every unit-twisted coupling row.
-/
theorem form_nonnegative_retwist_of_rowDomination
    (A : RowDiagonalDominationCarrier.RowAssembly Vertex Edge)
    (twist : Edge -> ℝ)
    (v : Vertex -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (hrow : ∀ i : Vertex, A.incidentBudget i <= A.diagonal i) :
    0 <= (retwist A twist).form v := by
  exact (retwist A twist).form_nonnegative_of_rowDomination v
    (fun i => by
      rw [incidentBudget_retwist_of_abs_twist_eq_one A twist htwist i]
      exact hrow i)

end RowAssembly

namespace SignedEdgeAssembly

open GlobalDominationReduction

variable {Vertex Edge : Type*} [Fintype Edge]

/-- Retwist every signed edge coupling by a scalar sign/phase. -/
def retwist (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (twist : Edge -> ℝ) : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge where
  left := A.left
  right := A.right
  coupling := fun e => twist e * A.coupling e

/-- Unit twists do not change the edgewise missing diagonal budget. -/
theorem missingDiagonalBudget_retwist_of_abs_twist_eq_one
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (twist : Edge -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (v : Vertex -> ℝ) :
    (retwist A twist).missingDiagonalBudget v = A.missingDiagonalBudget v := by
  unfold retwist GlobalDominationReduction.SignedEdgeAssembly.missingDiagonalBudget
  apply Finset.sum_congr rfl
  intro e _he
  unfold PrimeDominationBabyCarrier.weightedDiagonalBudget
  simp [abs_mul, htwist e]

/--
The global missing-diagonal reduction is also fake-family blind if the only
hypothesis is domination of the absolute missing budget.
-/
theorem completedByArch_nonnegative_retwist_of_archDomination
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (twist : Edge -> ℝ)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (hdom : A.missingDiagonalBudget v <= arch v) :
    0 <= (retwist A twist).completedByArch arch v := by
  exact (retwist A twist).archDomination_implies_completed_nonnegative arch v
    (by
      rw [missingDiagonalBudget_retwist_of_abs_twist_eq_one A twist htwist v]
      exact hdom)

end SignedEdgeAssembly

namespace StarAssembly

open SchurStarDominationCarrier

variable {Edge : Type*} [Fintype Edge]

/-- Retwist every Schur-star response coefficient by a scalar sign/phase. -/
def retwist (A : SchurStarDominationCarrier.StarAssembly Edge)
    (twist : Edge -> ℝ) : SchurStarDominationCarrier.StarAssembly Edge where
  arch := A.arch
  root := A.root
  response := fun e => twist e * A.response e

/-- Unit twists do not change the Schur-star response budget. -/
theorem responseBudget_retwist_of_abs_twist_eq_one
    (A : SchurStarDominationCarrier.StarAssembly Edge)
    (twist : Edge -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1) :
    (retwist A twist).responseBudget = A.responseBudget := by
  unfold retwist SchurStarDominationCarrier.StarAssembly.responseBudget
  apply Finset.sum_congr rfl
  intro e _he
  have hsq : twist e ^ 2 = 1 := by
    have habs_sq : |twist e| ^ 2 = (1 : ℝ) := by
      rw [htwist e]
      norm_num
    rw [sq_abs] at habs_sq
    exact habs_sq
  rw [mul_pow]
  rw [hsq]
  ring

/--
The Schur response-budget certificate is fake-family blind under unit response
twists: the same response budget proves every sign-twisted star nonnegative.
-/
theorem form_nonnegative_retwist_of_responseBudget_le_arch
    (A : SchurStarDominationCarrier.StarAssembly Edge)
    (twist : Edge -> ℝ)
    (x : ℝ)
    (y : Edge -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (harch : 0 < A.arch)
    (hbudget : A.responseBudget <= A.arch) :
    0 <= (retwist A twist).form x y := by
  exact (retwist A twist).form_nonnegative_of_responseBudget_le_arch x y harch
    (by
      rw [responseBudget_retwist_of_abs_twist_eq_one A twist htwist]
      exact hbudget)

end StarAssembly

end AbsoluteBudgetFakeFamilyBlindness
end JensenLadder
