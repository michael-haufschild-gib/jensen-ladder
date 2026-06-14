import JensenLadder.CCMFiniteWeil
import Mathlib.Tactic

/-!
# Finite prime perturbation row bounds

This module turns the finite CCM/Sonin prime rows from `CCMFiniteWeil` into a
concrete perturbation-radius interface.  The main bound is the elementary
finite-dimensional estimate

```text
|Σ_j P[i,j] v[j]| <= Σ_j |P[i,j]| <= radius,    when ||v||_∞ <= 1.
```

The decomposed row sum

```text
Σ_j Σ_q |c_q K_q[i,j]|
```

is the certificate-friendly quantity: it bounds the absolute row sum of the
assembled prime perturbation even when the local rows have cancellations.

This file proves only finite algebra.  It does not prove a spectral norm
estimate, Kato smallness, finite-to-limit convergence, positivity, or the
Riemann Hypothesis.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMPerturbationBound

open scoped BigOperators
open CCMFiniteWeil

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The finite prime perturbation matrix acting on a vector. -/
noncomputable def primeOperator
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (v : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j : ι, primePart D i j * v j

/-- Absolute row sum of the assembled finite prime perturbation. -/
noncomputable def primeRowAbsSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) : ℝ :=
  ∑ j : ι, |primePart D i j|

/-- Certificate-friendly absolute row sum before cancellations between local
prime rows. -/
noncomputable def decomposedPrimeRowAbsSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) : ℝ :=
  ∑ j : ι, ∑ q : κ, |D.primeCoeff q * D.primeKernel q i j|

/-- Supremum-norm unit ball, written pointwise for finite vectors. -/
def SupNormLeOne (v : ι → ℝ) : Prop :=
  ∀ i : ι, |v i| ≤ 1

/-- A scalar radius bounds every assembled absolute row sum. -/
def RowBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radius : ℝ) : Prop :=
  ∀ i : ι, primeRowAbsSum D i ≤ radius

/-- A scalar radius bounds every decomposed local-row absolute sum. -/
def DecomposedRowBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radius : ℝ) : Prop :=
  ∀ i : ι, decomposedPrimeRowAbsSum D i ≤ radius

/-- Absolute row sums are nonnegative. -/
theorem primeRowAbsSum_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) :
    0 ≤ primeRowAbsSum D i := by
  unfold primeRowAbsSum
  exact Finset.sum_nonneg (fun j _ => abs_nonneg (primePart D i j))

/-- Decomposed absolute row sums are nonnegative. -/
theorem decomposedPrimeRowAbsSum_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) :
    0 ≤ decomposedPrimeRowAbsSum D i := by
  unfold decomposedPrimeRowAbsSum
  exact Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun q _ =>
      abs_nonneg (D.primeCoeff q * D.primeKernel q i j)))

/-- The assembled prime entry is bounded by the sum of local-row magnitudes. -/
theorem primePart_abs_le_decomposed
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i j : ι) :
    |primePart D i j| ≤
      ∑ q : κ, |D.primeCoeff q * D.primeKernel q i j| := by
  simpa [primePart] using
    (Finset.abs_sum_le_sum_abs
      (fun q : κ => D.primeCoeff q * D.primeKernel q i j)
      Finset.univ)

/-- The assembled absolute row sum is bounded by the decomposed certificate row
sum. -/
theorem primeRowAbsSum_le_decomposedPrimeRowAbsSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) :
    primeRowAbsSum D i ≤ decomposedPrimeRowAbsSum D i := by
  unfold primeRowAbsSum decomposedPrimeRowAbsSum
  exact Finset.sum_le_sum (fun j _ =>
    primePart_abs_le_decomposed D i j)

/-- A decomposed row bound is an assembled row bound. -/
theorem rowBound_of_decomposedRowBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radius : ℝ}
    (hrow : DecomposedRowBound D radius) :
    RowBound D radius := by
  intro i
  exact le_trans (primeRowAbsSum_le_decomposedPrimeRowAbsSum D i) (hrow i)

/-- Absolute row-sum control bounds each component of the finite prime
perturbation on the sup-norm unit ball. -/
theorem abs_primeOperator_le_primeRowAbsSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    {v : ι → ℝ}
    (hv : SupNormLeOne v)
    (i : ι) :
    |primeOperator D v i| ≤ primeRowAbsSum D i := by
  calc
    |primeOperator D v i| =
        |∑ j : ι, primePart D i j * v j| := by
          rfl
    _ ≤ ∑ j : ι, |primePart D i j * v j| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (fun j : ι => primePart D i j * v j)
          Finset.univ)
    _ = ∑ j : ι, |primePart D i j| * |v j| := by
      simp [abs_mul]
    _ ≤ ∑ j : ι, |primePart D i j| := by
      exact Finset.sum_le_sum (fun j _ =>
        mul_le_of_le_one_right (abs_nonneg (primePart D i j)) (hv j))
    _ = primeRowAbsSum D i := by
      rfl

/-- A row-bound radius controls every component of the finite prime
perturbation on the sup-norm unit ball. -/
theorem abs_primeOperator_le_radius
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radius : ℝ}
    (hrow : RowBound D radius)
    {v : ι → ℝ}
    (hv : SupNormLeOne v)
    (i : ι) :
    |primeOperator D v i| ≤ radius :=
  le_trans (abs_primeOperator_le_primeRowAbsSum D hv i) (hrow i)

/-- A decomposed local-row radius controls every component of the finite prime
perturbation on the sup-norm unit ball. -/
theorem abs_primeOperator_le_radius_of_decomposedRowBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radius : ℝ}
    (hrow : DecomposedRowBound D radius)
    {v : ι → ℝ}
    (hv : SupNormLeOne v)
    (i : ι) :
    |primeOperator D v i| ≤ radius :=
  abs_primeOperator_le_radius
    (rowBound_of_decomposedRowBound hrow) hv i

end CCMPerturbationBound
end JensenLadder
