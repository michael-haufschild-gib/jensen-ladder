import JensenLadder.PrimeDominationBabyCarrier
import Mathlib.Tactic

/-!
# Graph Laplacian square-root baby carrier

This module records a finite incidence-factorization baby carrier.

An edge `e` has endpoints `left e`, `right e`, and a real square-root weight
`root e`.  Its Laplacian weight is `root e ^ 2`, hence nonnegative by
construction.  The associated quadratic form is

```text
  sum_e root(e)^2 * (v(left e) - v(right e))^2,
```

which is exactly the square norm of the first-order incidence operator

```text
  (Dv)_e = root(e) * (v(left e) - v(right e)).
```

The same edge expansion supplies the diagonal domination inequality

```text
  2 * root(e)^2 * |x*y| <= root(e)^2*x^2 + root(e)^2*y^2.
```

This is not a proof of RH and not a global arithmetic carrier.  It is a formal
finite model of the square-root/domination mechanisms requested in the carrier
prompt.  Theorem M is proven, but Theorem M does not prove RH by itself.

Evidence class: formal/certificate artifact; proved lemma.
-/

namespace JensenLadder
namespace GraphLaplacianBabyCarrier

/-- A finite edge-indexed incidence assembly with built-in square-root weights. -/
structure RootedIncidenceAssembly (Vertex Edge : Type*) where
  left : Edge -> Vertex
  right : Edge -> Vertex
  root : Edge -> ℝ

namespace RootedIncidenceAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/-- The nonnegative Laplacian edge weight supplied by the square root. -/
def edgeWeight (A : RootedIncidenceAssembly Vertex Edge) (e : Edge) : ℝ :=
  A.root e ^ 2

/-- The first-order weighted incidence value on one edge. -/
def incidenceValue (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) : ℝ :=
  A.root e * (v (A.left e) - v (A.right e))

/-- The graph-Laplacian quadratic form. -/
def energy (A : RootedIncidenceAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    A.edgeWeight e * (v (A.left e) - v (A.right e)) ^ 2

/-- The square norm of the first-order incidence operator. -/
def squareNorm (A : RootedIncidenceAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, A.incidenceValue v e ^ 2

/-- The expanded contribution of one weighted edge. -/
def expandedEdge (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) : ℝ :=
  A.edgeWeight e * v (A.left e) ^ 2
    - 2 * A.edgeWeight e * v (A.left e) * v (A.right e)
    + A.edgeWeight e * v (A.right e) ^ 2

/-- The assembled expanded Laplacian form. -/
def expandedEnergy (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, A.expandedEdge v e

/-- The absolute off-diagonal budget of the expanded edge terms. -/
def offDiagonalAbsBudget (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    2 * A.edgeWeight e * |v (A.left e) * v (A.right e)|

/-- The diagonal budget supplied by the weighted incidence squares. -/
def diagonalBudget (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    (A.edgeWeight e * v (A.left e) ^ 2
      + A.edgeWeight e * v (A.right e) ^ 2)

omit [Fintype Edge] in
/-- Every edge weight is nonnegative because it is a square. -/
theorem edgeWeight_nonnegative (A : RootedIncidenceAssembly Vertex Edge)
    (e : Edge) :
    0 <= A.edgeWeight e := by
  unfold edgeWeight
  exact sq_nonneg (A.root e)

omit [Fintype Edge] in
/-- One edge's Laplacian energy is exactly one incidence square. -/
theorem edge_energy_eq_square
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    A.edgeWeight e * (v (A.left e) - v (A.right e)) ^ 2
      = A.incidenceValue v e ^ 2 := by
  unfold edgeWeight incidenceValue
  ring

/-- The whole finite Laplacian form is the square norm of incidence. -/
theorem energy_eq_squareNorm
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.energy v = A.squareNorm v := by
  unfold energy squareNorm
  exact Finset.sum_congr rfl (fun e _ =>
    edge_energy_eq_square A v e)

/-- The square-root/incidence factorization proves nonnegativity. -/
theorem energy_nonnegative
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    0 <= A.energy v := by
  rw [energy_eq_squareNorm]
  unfold squareNorm
  exact Finset.sum_nonneg (fun e _ => sq_nonneg (A.incidenceValue v e))

omit [Fintype Edge] in
/-- One edge's weighted square expands into diagonal terms plus a cross term. -/
theorem edge_energy_eq_expanded
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    A.edgeWeight e * (v (A.left e) - v (A.right e)) ^ 2
      = A.expandedEdge v e := by
  unfold expandedEdge edgeWeight
  ring_nf

/-- The finite energy equals its expanded diagonal/off-diagonal form. -/
theorem energy_eq_expandedEnergy
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.energy v = A.expandedEnergy v := by
  unfold energy expandedEnergy
  exact Finset.sum_congr rfl (fun e _ =>
    edge_energy_eq_expanded A v e)

omit [Fintype Edge] in
/-- Each edge's off-diagonal magnitude is dominated by its own diagonal budget. -/
theorem edge_offDiagonal_dominated
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    2 * A.edgeWeight e * |v (A.left e) * v (A.right e)|
      <= A.edgeWeight e * v (A.left e) ^ 2
        + A.edgeWeight e * v (A.right e) ^ 2 := by
  have hxy :
      2 * |v (A.left e) * v (A.right e)|
        <= v (A.left e) ^ 2 + v (A.right e) ^ 2 :=
    JensenLadder.PrimeDominationBabyCarrier.two_abs_mul_le_sq_add_sq
      (v (A.left e)) (v (A.right e))
  have hw : 0 <= A.edgeWeight e := A.edgeWeight_nonnegative e
  calc
    2 * A.edgeWeight e * |v (A.left e) * v (A.right e)|
        = A.edgeWeight e * (2 * |v (A.left e) * v (A.right e)|) := by
          ring
    _ <= A.edgeWeight e * (v (A.left e) ^ 2 + v (A.right e) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hxy hw
    _ = A.edgeWeight e * v (A.left e) ^ 2
        + A.edgeWeight e * v (A.right e) ^ 2 := by
          ring

/-- The assembled off-diagonal budget is dominated by the assembled diagonal budget. -/
theorem offDiagonalAbsBudget_le_diagonalBudget
    (A : RootedIncidenceAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.offDiagonalAbsBudget v <= A.diagonalBudget v := by
  unfold offDiagonalAbsBudget diagonalBudget
  exact Finset.sum_le_sum (fun e _ =>
    A.edge_offDiagonal_dominated v e)

end RootedIncidenceAssembly

end GraphLaplacianBabyCarrier
end JensenLadder
