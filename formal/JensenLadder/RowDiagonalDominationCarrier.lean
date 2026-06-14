import JensenLadder.GlobalDominationReduction
import Mathlib.Tactic

/-!
# Row diagonal domination carrier

This module records the finite row-wise domination certificate behind the
prompt's domination phrasing.

Each signed edge coupling `c_e` contributes an off-diagonal term

```text
  2*c_e*v(left e)*v(right e).
```

If each vertex diagonal coefficient dominates the sum of absolute couplings
incident to that vertex, then the whole signed quadratic form is nonnegative.
This is the finite Gershgorin/M-matrix style certificate.

This does not prove that the zeta Weil form satisfies the required row
domination.  It is a formal carrier-area baby theorem: if a carrier supplies
the row bound structurally, positivity follows without any hypothesis about
zeta zeros.  Theorem M is proven, but Theorem M does not prove RH by itself.

Evidence class: formal/certificate artifact; proved lemma.
-/

namespace JensenLadder
namespace RowDiagonalDominationCarrier

/-- A finite signed edge row with an explicit vertex diagonal. -/
structure RowAssembly (Vertex Edge : Type*) where
  left : Edge -> Vertex
  right : Edge -> Vertex
  coupling : Edge -> ℝ
  diagonal : Vertex -> ℝ

namespace RowAssembly

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]

/-- The absolute incident-coupling budget at one vertex. -/
def incidentBudget (A : RowAssembly Vertex Edge) (i : Vertex) : ℝ :=
  ∑ e : Edge,
    ((if A.left e = i then |A.coupling e| else 0)
      + (if A.right e = i then |A.coupling e| else 0))

/-- The vertex-diagonal quadratic form. -/
def diagonalForm (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ i : Vertex, A.diagonal i * v i ^ 2

/-- The same row budget, already regrouped as a quadratic form. -/
def incidentBudgetForm (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ i : Vertex, A.incidentBudget i * v i ^ 2

/-- The edgewise missing diagonal budget before regrouping by rows. -/
def missingDiagonalBudget (A : RowAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    (|A.coupling e| * v (A.left e) ^ 2
      + |A.coupling e| * v (A.right e) ^ 2)

/-- The signed off-diagonal row. -/
def offDiagonalRow (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, 2 * A.coupling e * v (A.left e) * v (A.right e)

/-- The completed row-dominated finite quadratic form. -/
def form (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  A.diagonalForm v + A.offDiagonalRow v

omit [Fintype Edge] in
/-- A left endpoint contribution can be written as a vertex sum. -/
theorem left_endpoint_budget_as_vertex_sum
    (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) (e : Edge) :
    (∑ i : Vertex,
      (if A.left e = i then |A.coupling e| * v i ^ 2 else 0))
      = |A.coupling e| * v (A.left e) ^ 2 := by
  simp

omit [Fintype Edge] in
/-- A right endpoint contribution can be written as a vertex sum. -/
theorem right_endpoint_budget_as_vertex_sum
    (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) (e : Edge) :
    (∑ i : Vertex,
      (if A.right e = i then |A.coupling e| * v i ^ 2 else 0))
      = |A.coupling e| * v (A.right e) ^ 2 := by
  simp

/-- The edgewise missing diagonal budget regroups exactly into row budgets. -/
theorem missingDiagonalBudget_eq_incidentBudgetForm
    (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) :
    A.missingDiagonalBudget v = A.incidentBudgetForm v := by
  unfold missingDiagonalBudget incidentBudgetForm incidentBudget
  calc
    (∑ e : Edge,
      (|A.coupling e| * v (A.left e) ^ 2
        + |A.coupling e| * v (A.right e) ^ 2))
        = ∑ e : Edge,
            ((∑ i : Vertex,
                (if A.left e = i then |A.coupling e| * v i ^ 2 else 0))
              + (∑ i : Vertex,
                (if A.right e = i then |A.coupling e| * v i ^ 2 else 0))) := by
          apply Finset.sum_congr rfl
          intro e _he
          rw [left_endpoint_budget_as_vertex_sum A v e,
            right_endpoint_budget_as_vertex_sum A v e]
    _ = ∑ e : Edge, ∑ i : Vertex,
            ((if A.left e = i then |A.coupling e| * v i ^ 2 else 0)
              + (if A.right e = i then |A.coupling e| * v i ^ 2 else 0)) := by
          simp [Finset.sum_add_distrib]
    _ = ∑ i : Vertex, ∑ e : Edge,
            ((if A.left e = i then |A.coupling e| * v i ^ 2 else 0)
              + (if A.right e = i then |A.coupling e| * v i ^ 2 else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Vertex,
            (∑ e : Edge,
              ((if A.left e = i then |A.coupling e| else 0)
                + (if A.right e = i then |A.coupling e| else 0))) * v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e _he
          split <;> split <;> ring

/--
If every vertex diagonal dominates its incident absolute row budget, then the
edgewise missing diagonal budget is dominated by the vertex diagonal form.
-/
theorem missingDiagonalBudget_le_diagonalForm_of_rowDomination
    (A : RowAssembly Vertex Edge)
    (v : Vertex -> ℝ)
    (hrow : ∀ i : Vertex, A.incidentBudget i <= A.diagonal i) :
    A.missingDiagonalBudget v <= A.diagonalForm v := by
  rw [missingDiagonalBudget_eq_incidentBudgetForm]
  unfold incidentBudgetForm diagonalForm
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (v i)))

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- The signed off-diagonal row is bounded below by the negative missing budget. -/
theorem offDiagonalRow_ge_neg_missingDiagonalBudget
    (A : RowAssembly Vertex Edge) (v : Vertex -> ℝ) :
    - A.missingDiagonalBudget v <= A.offDiagonalRow v := by
  unfold missingDiagonalBudget offDiagonalRow
  have hsum :
      (∑ e : Edge,
        - PrimeDominationBabyCarrier.weightedDiagonalBudget
            (A.coupling e) (v (A.left e)) (v (A.right e)))
        <= ∑ e : Edge, 2 * A.coupling e * v (A.left e) * v (A.right e) :=
    Finset.sum_le_sum (fun e _ =>
      GlobalDominationReduction.SignedEdgeAssembly.edge_offDiagonal_ge_neg_missingBudget
        { left := A.left, right := A.right, coupling := A.coupling } v e)
  rw [Finset.sum_neg_distrib] at hsum
  unfold PrimeDominationBabyCarrier.weightedDiagonalBudget at hsum
  exact hsum

/--
Finite row diagonal domination proves nonnegativity of the signed quadratic
form.
-/
theorem form_nonnegative_of_rowDomination
    (A : RowAssembly Vertex Edge)
    (v : Vertex -> ℝ)
    (hrow : ∀ i : Vertex, A.incidentBudget i <= A.diagonal i) :
    0 <= A.form v := by
  have hmiss : A.missingDiagonalBudget v <= A.diagonalForm v :=
    A.missingDiagonalBudget_le_diagonalForm_of_rowDomination v hrow
  have hoff : - A.missingDiagonalBudget v <= A.offDiagonalRow v :=
    A.offDiagonalRow_ge_neg_missingDiagonalBudget v
  unfold form
  linarith

end RowAssembly

end RowDiagonalDominationCarrier
end JensenLadder
