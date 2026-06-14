import JensenLadder.CCMPerturbationBound
import Mathlib.Tactic

/-!
# Frobenius-square bounds for finite CCM prime perturbations

This module upgrades the componentwise row control in `CCMPerturbationBound` to
a finite `l²`-squared estimate.  For the assembled prime perturbation `P`, it
proves the finite-dimensional Frobenius bound

```text
Σ_i |(P v)_i|² <= (Σ_i Σ_j |P_ij|²) * Σ_j |v_j|².
```

It also records a decomposed certificate bound where each assembled entry is
dominated by the local prime rows before cancellation:

```text
|P_ij|² <= (Σ_q |c_q K_q[i,j]|)².
```

This is still finite algebra only.  It does not prove spectral convergence,
Kato smallness, ground-state simplicity, positivity, or the Riemann Hypothesis.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMFrobeniusBound

open scoped BigOperators
open CCMFiniteWeil
open CCMPerturbationBound

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Squared Euclidean norm for a finite real vector. -/
noncomputable def sqNorm (v : ι → ℝ) : ℝ :=
  ∑ i : ι, v i ^ 2

/-- Squared `l²` row norm of the assembled finite prime perturbation. -/
noncomputable def primeRowSqSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) : ℝ :=
  ∑ j : ι, (primePart D i j) ^ 2

/-- Frobenius-square size of the assembled finite prime perturbation. -/
noncomputable def primeFrobeniusSq
    (D : SemilocalFiniteWeilData ι κ ℝ) : ℝ :=
  ∑ i : ι, primeRowSqSum D i

/-- Local-prime absolute entry sum before cancellations. -/
noncomputable def decomposedPrimeEntryAbsSum
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i j : ι) : ℝ :=
  ∑ q : κ, |D.primeCoeff q * D.primeKernel q i j|

/-- Certificate-friendly Frobenius-square size before local-row cancellations. -/
noncomputable def decomposedPrimeFrobeniusSq
    (D : SemilocalFiniteWeilData ι κ ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, (decomposedPrimeEntryAbsSum D i j) ^ 2

/-- A scalar square-radius bounds the assembled Frobenius-square size. -/
def FrobeniusSqBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radiusSq : ℝ) : Prop :=
  primeFrobeniusSq D ≤ radiusSq

/-- A scalar square-radius bounds the decomposed certificate Frobenius-square
size. -/
def DecomposedFrobeniusSqBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radiusSq : ℝ) : Prop :=
  decomposedPrimeFrobeniusSq D ≤ radiusSq

/-- Squared-operator bound in finite `l²` form. -/
def L2SqOperatorBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radiusSq : ℝ) : Prop :=
  ∀ v : ι → ℝ,
    sqNorm (primeOperator D v) ≤ radiusSq * sqNorm v

/-- Squared norms are nonnegative. -/
theorem sqNorm_nonneg
    (v : ι → ℝ) :
    0 ≤ sqNorm v := by
  unfold sqNorm
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

/-- Squared row sums are nonnegative. -/
theorem primeRowSqSum_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i : ι) :
    0 ≤ primeRowSqSum D i := by
  unfold primeRowSqSum
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (primePart D i j))

/-- The assembled Frobenius-square size is nonnegative. -/
theorem primeFrobeniusSq_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ) :
    0 ≤ primeFrobeniusSq D := by
  unfold primeFrobeniusSq
  exact Finset.sum_nonneg (fun i _ => primeRowSqSum_nonneg D i)

/-- Decomposed entry absolute sums are nonnegative. -/
theorem decomposedPrimeEntryAbsSum_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i j : ι) :
    0 ≤ decomposedPrimeEntryAbsSum D i j := by
  unfold decomposedPrimeEntryAbsSum
  exact Finset.sum_nonneg (fun q _ =>
    abs_nonneg (D.primeCoeff q * D.primeKernel q i j))

/-- The decomposed Frobenius-square certificate size is nonnegative. -/
theorem decomposedPrimeFrobeniusSq_nonneg
    (D : SemilocalFiniteWeilData ι κ ℝ) :
    0 ≤ decomposedPrimeFrobeniusSq D := by
  unfold decomposedPrimeFrobeniusSq
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ =>
      sq_nonneg (decomposedPrimeEntryAbsSum D i j)))

/-- Each assembled prime entry square is bounded by the square of its decomposed
local-prime absolute entry sum. -/
theorem primePart_sq_le_decomposedPrimeEntryAbsSum_sq
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (i j : ι) :
    (primePart D i j) ^ 2 ≤
      (decomposedPrimeEntryAbsSum D i j) ^ 2 := by
  have hentry :
      |primePart D i j| ≤ decomposedPrimeEntryAbsSum D i j := by
    simpa [decomposedPrimeEntryAbsSum] using
      (primePart_abs_le_decomposed D i j)
  have hnonneg : 0 ≤ decomposedPrimeEntryAbsSum D i j :=
    decomposedPrimeEntryAbsSum_nonneg D i j
  rw [← sq_abs (primePart D i j)]
  exact sq_le_sq.mpr (by
    simpa [abs_abs, abs_of_nonneg hnonneg] using hentry)

/-- The assembled Frobenius-square size is bounded by the decomposed certificate
Frobenius-square size. -/
theorem primeFrobeniusSq_le_decomposedPrimeFrobeniusSq
    (D : SemilocalFiniteWeilData ι κ ℝ) :
    primeFrobeniusSq D ≤ decomposedPrimeFrobeniusSq D := by
  unfold primeFrobeniusSq primeRowSqSum decomposedPrimeFrobeniusSq
  exact Finset.sum_le_sum (fun i _ =>
    Finset.sum_le_sum (fun j _ =>
      primePart_sq_le_decomposedPrimeEntryAbsSum_sq D i j))

/-- A decomposed Frobenius-square certificate gives an assembled
Frobenius-square bound. -/
theorem frobeniusSqBound_of_decomposedFrobeniusSqBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radiusSq : ℝ}
    (hbound : DecomposedFrobeniusSqBound D radiusSq) :
    FrobeniusSqBound D radiusSq :=
  le_trans (primeFrobeniusSq_le_decomposedPrimeFrobeniusSq D) hbound

/-- Cauchy--Schwarz row estimate for one component of the finite prime
perturbation. -/
theorem primeOperator_component_sq_le_rowSqSum_mul_sqNorm
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (v : ι → ℝ)
    (i : ι) :
    (primeOperator D v i) ^ 2 ≤ primeRowSqSum D i * sqNorm v := by
  simpa [primeOperator, primeRowSqSum, sqNorm] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ι)
      (fun j : ι => primePart D i j)
      (fun j : ι => v j))

/-- Frobenius-square bound for the finite prime perturbation acting on a finite
real vector. -/
theorem sqNorm_primeOperator_le_frobeniusSq_mul_sqNorm
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (v : ι → ℝ) :
    sqNorm (primeOperator D v) ≤ primeFrobeniusSq D * sqNorm v := by
  calc
    sqNorm (primeOperator D v)
        = ∑ i : ι, (primeOperator D v i) ^ 2 := by
          rfl
    _ ≤ ∑ i : ι, primeRowSqSum D i * sqNorm v := by
      exact Finset.sum_le_sum (fun i _ =>
        primeOperator_component_sq_le_rowSqSum_mul_sqNorm D v i)
    _ = primeFrobeniusSq D * sqNorm v := by
      simpa [primeFrobeniusSq] using
        (Finset.sum_mul (Finset.univ)
          (fun i : ι => primeRowSqSum D i) (sqNorm v)).symm

/-- A Frobenius-square radius gives a finite `l²` squared-operator bound. -/
theorem l2SqOperatorBound_of_frobeniusSqBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radiusSq : ℝ}
    (hbound : FrobeniusSqBound D radiusSq) :
    L2SqOperatorBound D radiusSq := by
  intro v
  exact le_trans (sqNorm_primeOperator_le_frobeniusSq_mul_sqNorm D v)
    (mul_le_mul_of_nonneg_right hbound (sqNorm_nonneg v))

/-- A decomposed Frobenius-square certificate gives a finite `l²`
squared-operator bound. -/
theorem l2SqOperatorBound_of_decomposedFrobeniusSqBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radiusSq : ℝ}
    (hbound : DecomposedFrobeniusSqBound D radiusSq) :
    L2SqOperatorBound D radiusSq :=
  l2SqOperatorBound_of_frobeniusSqBound
    (frobeniusSqBound_of_decomposedFrobeniusSqBound hbound)

end CCMFrobeniusBound
end JensenLadder
