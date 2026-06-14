import JensenLadder.SchurStarDominationCarrier
import Mathlib.Tactic

/-!
# Schur star assembly carrier

This module proves that finite sums of Schur-star certificates are again
nonnegative.  Each star has its own central diagonal and response row, while
sharing a finite leaf index type for convenience.

This is a finite gluing/composition theorem for the carrier-area baby
certificates.  It does not identify any zeta Weil form with such an assembly
and does not prove RH.  Theorem M is proven, but Theorem M does not prove RH by
itself.

Evidence class: formal/certificate artifact; proved lemma.
-/

namespace JensenLadder
namespace SchurStarAssemblyCarrier

open SchurStarDominationCarrier

/-- A finite family of Schur-star blocks. -/
structure StarFamily (Star Leaf : Type*) where
  arch : Star -> ℝ
  root : Star -> Leaf -> ℝ
  response : Star -> Leaf -> ℝ

namespace StarFamily

variable {Star Leaf : Type*} [Fintype Star] [Fintype Leaf]

/-- The individual Schur-star block indexed by `s`. -/
def block (F : StarFamily Star Leaf) (s : Star) :
    SchurStarDominationCarrier.StarAssembly Leaf where
  arch := F.arch s
  root := F.root s
  response := F.response s

/-- The assembled finite Schur-star form. -/
def form (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ) : ℝ :=
  ∑ s : Star, (F.block s).form (x s) (y s)

/-- The assembled finite form after multiplying each star by its central diagonal. -/
def archWeightedForm (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ) : ℝ :=
  ∑ s : Star, (F.block s).arch * (F.block s).form (x s) (y s)

/-- The assembled square/projection right-hand side. -/
def squareProjectionSum (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ) : ℝ :=
  ∑ s : Star,
    (((F.block s).arch * x s + (F.block s).couplingSum (y s)) ^ 2
      + (F.block s).projectionResidual (y s))

/-- A finite assembly of response-budget-dominated Schur stars is nonnegative. -/
theorem form_nonnegative_of_responseBudget_le_arch
    (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ)
    (harch : ∀ s : Star, 0 < (F.block s).arch)
    (hbudget : ∀ s : Star, (F.block s).responseBudget <= (F.block s).arch) :
    0 <= F.form x y := by
  unfold form
  exact Finset.sum_nonneg (fun s _ =>
    (F.block s).form_nonnegative_of_responseBudget_le_arch
      (x s) (y s) (harch s) (hbudget s))

/-- The assembled square/projection identity, star by star. -/
theorem archWeightedForm_eq_squareProjectionSum
    (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ) :
    F.archWeightedForm x y = F.squareProjectionSum x y := by
  unfold archWeightedForm squareProjectionSum
  exact Finset.sum_congr rfl (fun s _ =>
    (F.block s).arch_mul_form_eq_square_add_projectionResidual (x s) (y s))

/-- The assembled square/projection right-hand side is nonnegative under the response budget. -/
theorem squareProjectionSum_nonnegative_of_responseBudget_le_arch
    (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ)
    (hbudget : ∀ s : Star, (F.block s).responseBudget <= (F.block s).arch) :
    0 <= F.squareProjectionSum x y := by
  unfold squareProjectionSum
  exact Finset.sum_nonneg (fun s _ =>
    add_nonneg (sq_nonneg _)
      ((F.block s).projectionResidual_nonnegative_of_responseBudget_le_arch
        (y s) (hbudget s)))

/-- The assembled arch-weighted form is nonnegative under the response budget. -/
theorem archWeightedForm_nonnegative_of_responseBudget_le_arch
    (F : StarFamily Star Leaf)
    (x : Star -> ℝ) (y : Star -> Leaf -> ℝ)
    (hbudget : ∀ s : Star, (F.block s).responseBudget <= (F.block s).arch) :
    0 <= F.archWeightedForm x y := by
  rw [F.archWeightedForm_eq_squareProjectionSum x y]
  exact F.squareProjectionSum_nonnegative_of_responseBudget_le_arch x y hbudget

end StarFamily

end SchurStarAssemblyCarrier
end JensenLadder
