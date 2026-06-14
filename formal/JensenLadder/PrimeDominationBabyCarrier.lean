import JensenLadder.PrimeLocalNoGo
import Mathlib.Tactic

/-!
# Prime domination baby carrier

This module records a deliberately small, unconditional carrier-area step.

`PrimeLocalNoGo` proves the negative half of the missing-diagonal story: the
one-sided finite-prime kernel, with its `m = 0` diagonal removed, is
sign-indefinite.  Here we prove the complementary positive baby statement:
after adjoining a normalized missing diagonal, a single off-diagonal arithmetic
coupling `r` with `|r| <= 1` is dominated by the diagonal and the resulting
two-mode block has an explicit square-root/eigenmode decomposition.

In matrix language this is the block

```text
  [1  r]
  [r  1]
```

acting on `(x,y)`.  The proof uses only `|r| <= 1`; it contains no hypothesis
about zeta zeros, Weil positivity, spectral faithfulness, or RH.  For a prime
power coupling the arithmetic input is precisely the elementary normalization
`r = p^{-m/2}`, hence `0 < r < 1`.

This is not a proof of RH and not a global carrier.  It is a formal baby
domination/square-root block showing exactly what the missing diagonal buys in
one local two-mode instance.  Theorem M is proven, but Theorem M does not prove
RH by itself.

Evidence class: formal/certificate artifact; proved lemma; dead-end companion
to the one-sided local no-go.
-/

namespace JensenLadder
namespace PrimeDominationBabyCarrier

/-- The diagonal-completed two-mode block with normalized off-diagonal coupling `r`. -/
def completedBlock (r x y : ℝ) : ℝ :=
  x ^ 2 + 2 * r * x * y + y ^ 2

/-- The diagonal-deleted off-diagonal part of the same two-mode block. -/
def diagonalDeletedBlock (r x y : ℝ) : ℝ :=
  2 * r * x * y

/-- The explicit eigenmode norm-square for the completed block. -/
noncomputable def eigenmodeNormSq (r x y : ℝ) : ℝ :=
  ((1 + r) / 2) * (x + y) ^ 2 + ((1 - r) / 2) * (x - y) ^ 2

/-- Elementary two-variable AM-GM in the absolute-value form needed below. -/
theorem two_abs_mul_le_sq_add_sq (x y : ℝ) :
    2 * |x * y| <= x ^ 2 + y ^ 2 := by
  have hsq : 0 <= (|x| - |y|) ^ 2 := sq_nonneg (|x| - |y|)
  have hx : |x| ^ 2 = x ^ 2 := by
    rw [sq_abs]
  have hy : |y| ^ 2 = y ^ 2 := by
    rw [sq_abs]
  rw [abs_mul]
  nlinarith

/--
One normalized off-diagonal row is dominated by the two diagonal entries.

This is the formal baby version of the requested domination phrasing:
`|prime/off-diagonal row| <= archimedean diagonal`, in a single normalized
two-mode block.  The only input is `|r| <= 1`.
-/
theorem offDiagonal_dominated_by_diagonal
    {r x y : ℝ}
    (hr : |r| <= 1) :
    2 * |r * x * y| <= x ^ 2 + y ^ 2 := by
  have hxy : 2 * |x * y| <= x ^ 2 + y ^ 2 :=
    two_abs_mul_le_sq_add_sq x y
  have habs : |r * x * y| <= |x * y| := by
    calc
      |r * x * y| = |r| * |x * y| := by
        rw [show r * x * y = r * (x * y) by ring, abs_mul]
      _ <= 1 * |x * y| := by
        exact mul_le_mul_of_nonneg_right hr (abs_nonneg (x * y))
      _ = |x * y| := by
        ring
  nlinarith

/-- The completed block is exactly its eigenmode norm-square decomposition. -/
theorem completedBlock_eq_eigenmodeNormSq (r x y : ℝ) :
    completedBlock r x y = eigenmodeNormSq r x y := by
  unfold completedBlock eigenmodeNormSq
  ring

/--
The completed two-mode block is nonnegative whenever `|r| <= 1`.

This is the square-root/eigenmode phrasing: the block is a nonnegative weighted
sum of two squares, with weights `(1+r)/2` and `(1-r)/2`.
-/
theorem completedBlock_nonnegative_of_abs_le_one
    {r x y : ℝ}
    (hr : |r| <= 1) :
    0 <= completedBlock r x y := by
  have hrange := abs_le.mp hr
  have hplus : 0 <= 1 + r := by
    linarith
  have hminus : 0 <= 1 - r := by
    linarith
  rw [completedBlock_eq_eigenmodeNormSq]
  unfold eigenmodeNormSq
  positivity

/-- A coupling in `[-1,1]` gives the same completed-block nonnegativity. -/
theorem completedBlock_nonnegative_of_mem_interval
    {r x y : ℝ}
    (hrlo : -1 <= r)
    (hrhi : r <= 1) :
    0 <= completedBlock r x y := by
  exact completedBlock_nonnegative_of_abs_le_one
    (abs_le.mpr ⟨hrlo, hrhi⟩)

/--
The diagonal-deleted off-diagonal piece can already be negative in the
two-mode baby model.

This is the local-no-go companion to the domination theorem: the missing
diagonal is doing real work.
-/
theorem diagonalDeletedBlock_negative_at_opposite_modes
    {r : ℝ}
    (hr : 0 < r) :
    diagonalDeletedBlock r 1 (-1) < 0 := by
  unfold diagonalDeletedBlock
  nlinarith

/--
A packaged two-mode domination carrier.

`coupling_abs_le_one` is the only structural input.  For prime-power rows this
is supplied by the elementary arithmetic bound on the normalized coefficient.
-/
structure TwoModeCarrier where
  coupling : ℝ
  coupling_abs_le_one : |coupling| <= 1

namespace TwoModeCarrier

/-- The carrier's completed quadratic block. -/
def form (C : TwoModeCarrier) (x y : ℝ) : ℝ :=
  completedBlock C.coupling x y

/-- The carrier's explicit square-root/eigenmode norm-square. -/
noncomputable def squareNorm (C : TwoModeCarrier) (x y : ℝ) : ℝ :=
  eigenmodeNormSq C.coupling x y

/-- The carrier's square-root/eigenmode identity. -/
theorem square_identity (C : TwoModeCarrier) (x y : ℝ) :
    C.form x y = C.squareNorm x y := by
  unfold form squareNorm
  exact completedBlock_eq_eigenmodeNormSq C.coupling x y

/-- The carrier proves nonnegativity of its completed block. -/
theorem form_nonnegative (C : TwoModeCarrier) (x y : ℝ) :
    0 <= C.form x y := by
  unfold form
  exact completedBlock_nonnegative_of_abs_le_one C.coupling_abs_le_one

/-- The carrier proves domination of the normalized off-diagonal row. -/
theorem offDiagonal_dominated (C : TwoModeCarrier) (x y : ℝ) :
    2 * |C.coupling * x * y| <= x ^ 2 + y ^ 2 :=
  offDiagonal_dominated_by_diagonal C.coupling_abs_le_one

end TwoModeCarrier

end PrimeDominationBabyCarrier
end JensenLadder

namespace JensenLadder
namespace PrimeDominationBabyCarrier

/-!
## Finite assembly of completed two-mode blocks

This is the next baby step after `TwoModeCarrier`: a finite edge-indexed
assembly of completed rank-two blocks.  Vertices may be shared between edges,
but each edge brings its own two diagonal contributions.  Hence the global form
is a finite sum of already-certified square blocks.
-/

/-- A finite assembly of completed two-mode blocks over an abstract edge set. -/
structure FiniteBlockAssembly (Vertex Edge : Type*) where
  left : Edge -> Vertex
  right : Edge -> Vertex
  block : Edge -> TwoModeCarrier

namespace FiniteBlockAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/-- The assembled completed-block quadratic form. -/
def form (A : FiniteBlockAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, (A.block e).form (v (A.left e)) (v (A.right e))

/-- The assembled explicit square/eigenmode norm. -/
noncomputable def squareNorm (A : FiniteBlockAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, (A.block e).squareNorm (v (A.left e)) (v (A.right e))

/-- The assembled diagonal-deleted absolute off-diagonal budget. -/
def offDiagonalAbsBudget (A : FiniteBlockAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    2 * |(A.block e).coupling * v (A.left e) * v (A.right e)|

/-- The assembled diagonal budget contributed by the completed blocks. -/
def diagonalBudget (A : FiniteBlockAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, (v (A.left e) ^ 2 + v (A.right e) ^ 2)

/-- The finite assembly inherits the square/eigenmode identity edge by edge. -/
theorem square_identity (A : FiniteBlockAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.form v = A.squareNorm v := by
  unfold form squareNorm
  exact Finset.sum_congr rfl (fun e _ =>
    TwoModeCarrier.square_identity (A.block e) (v (A.left e)) (v (A.right e)))

/-- A finite assembly of completed two-mode carriers is nonnegative. -/
theorem form_nonnegative (A : FiniteBlockAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    0 <= A.form v := by
  unfold form
  exact Finset.sum_nonneg (fun e _ =>
    TwoModeCarrier.form_nonnegative (A.block e) (v (A.left e)) (v (A.right e)))

/-- The assembled off-diagonal absolute budget is dominated by its diagonal budget. -/
theorem offDiagonalAbsBudget_le_diagonalBudget
    (A : FiniteBlockAssembly Vertex Edge) (v : Vertex -> ℝ) :
    A.offDiagonalAbsBudget v <= A.diagonalBudget v := by
  unfold offDiagonalAbsBudget diagonalBudget
  exact Finset.sum_le_sum (fun e _ =>
    TwoModeCarrier.offDiagonal_dominated (A.block e) (v (A.left e)) (v (A.right e)))

end FiniteBlockAssembly

end PrimeDominationBabyCarrier
end JensenLadder

namespace JensenLadder
namespace PrimeDominationBabyCarrier

/-!
## Diagonal-budget assembly

This variant exposes the diagonal budget explicitly.  An arbitrary off-diagonal
coefficient `c` is controlled by spending `|c|` units of diagonal weight on each
endpoint.  Finite sums of such budgeted edge blocks are nonnegative, with any
additional nonnegative surplus diagonal allowed.
-/

/-- A completed edge block with the exact absolute diagonal budget for coupling `c`. -/
def weightedCompletedBlock (c x y : ℝ) : ℝ :=
  |c| * x ^ 2 + 2 * c * x * y + |c| * y ^ 2

/-- The absolute off-diagonal part of a weighted edge block. -/
def weightedOffDiagonalAbs (c x y : ℝ) : ℝ :=
  2 * |c * x * y|

/-- The exact diagonal budget spent by a weighted edge block. -/
def weightedDiagonalBudget (c x y : ℝ) : ℝ :=
  |c| * x ^ 2 + |c| * y ^ 2

/-- An arbitrary weighted off-diagonal row is dominated by its absolute diagonal budget. -/
theorem weightedOffDiagonalAbs_le_weightedDiagonalBudget (c x y : ℝ) :
    weightedOffDiagonalAbs c x y <= weightedDiagonalBudget c x y := by
  have hxy : 2 * |x * y| <= x ^ 2 + y ^ 2 := two_abs_mul_le_sq_add_sq x y
  have hmul := mul_le_mul_of_nonneg_left hxy (abs_nonneg c)
  unfold weightedOffDiagonalAbs weightedDiagonalBudget
  calc
    2 * |c * x * y| = |c| * (2 * |x * y|) := by
      rw [show c * x * y = c * (x * y) by ring, abs_mul]
      ring
    _ <= |c| * (x ^ 2 + y ^ 2) := hmul
    _ = |c| * x ^ 2 + |c| * y ^ 2 := by
      ring

/-- A weighted completed edge block is nonnegative. -/
theorem weightedCompletedBlock_nonnegative (c x y : ℝ) :
    0 <= weightedCompletedBlock c x y := by
  have hdom : 2 * |c * x * y| <= |c| * (x ^ 2 + y ^ 2) := by
    have hxy : 2 * |x * y| <= x ^ 2 + y ^ 2 := two_abs_mul_le_sq_add_sq x y
    have hmul := mul_le_mul_of_nonneg_left hxy (abs_nonneg c)
    calc
      2 * |c * x * y| = |c| * (2 * |x * y|) := by
        rw [show c * x * y = c * (x * y) by ring, abs_mul]
        ring
      _ <= |c| * (x ^ 2 + y ^ 2) := hmul
  have hneg : - (2 * |c * x * y|) <= 2 * c * x * y := by
    have h0 : - |c * x * y| <= c * x * y := neg_abs_le (c * x * y)
    nlinarith
  unfold weightedCompletedBlock
  nlinarith

/-- A finite assembly with explicit per-edge diagonal budgets and surplus diagonal. -/
structure DiagonalBudgetAssembly (Vertex Edge : Type*) where
  left : Edge -> Vertex
  right : Edge -> Vertex
  coupling : Edge -> ℝ
  surplus : Vertex -> ℝ
  surplus_nonnegative : ∀ i : Vertex, 0 <= surplus i

namespace DiagonalBudgetAssembly

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]

/-- The finite form with surplus diagonal plus edgewise absolute diagonal budgets. -/
def form (A : DiagonalBudgetAssembly Vertex Edge) (v : Vertex -> ℝ) : ℝ :=
  (∑ i : Vertex, A.surplus i * v i ^ 2) +
    ∑ e : Edge,
      weightedCompletedBlock (A.coupling e) (v (A.left e)) (v (A.right e))

/-- The assembled absolute off-diagonal budget. -/
def offDiagonalAbsBudget (A : DiagonalBudgetAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    weightedOffDiagonalAbs (A.coupling e) (v (A.left e)) (v (A.right e))

/-- The assembled edgewise diagonal budget, not counting surplus. -/
def edgeDiagonalBudget (A : DiagonalBudgetAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    weightedDiagonalBudget (A.coupling e) (v (A.left e)) (v (A.right e))

/-- A finite diagonal-budget assembly is nonnegative. -/
theorem form_nonnegative (A : DiagonalBudgetAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    0 <= A.form v := by
  unfold form
  apply add_nonneg
  · exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (A.surplus_nonnegative i) (sq_nonneg (v i)))
  · exact Finset.sum_nonneg (fun e _ =>
      weightedCompletedBlock_nonnegative (A.coupling e) (v (A.left e)) (v (A.right e)))

/-- The assembled off-diagonal budget is dominated by the edgewise diagonal budget. -/
theorem offDiagonalAbsBudget_le_edgeDiagonalBudget
    (A : DiagonalBudgetAssembly Vertex Edge) (v : Vertex -> ℝ) :
    A.offDiagonalAbsBudget v <= A.edgeDiagonalBudget v := by
  have _hvertexCard : 0 <= Fintype.card Vertex := Nat.zero_le _
  unfold offDiagonalAbsBudget edgeDiagonalBudget
  exact Finset.sum_le_sum (fun e _ =>
    weightedOffDiagonalAbs_le_weightedDiagonalBudget
      (A.coupling e) (v (A.left e)) (v (A.right e)))

end DiagonalBudgetAssembly

end PrimeDominationBabyCarrier
end JensenLadder
