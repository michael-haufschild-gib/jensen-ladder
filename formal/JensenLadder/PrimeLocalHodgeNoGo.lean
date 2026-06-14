import JensenLadder.PrimeLocalNoGo
import JensenLadder.HodgeWeilBridge

/-!
# One-sided prime-local Hodge no-go

This module connects the finite-prime local sign obstruction to the finite
Hodge-to-Weil bridge.

The construction below uses `CCMFiniteWeil.SemilocalFiniteWeilData` only as a
finite matrix container.  It does **not** interpret the one-point matrix as the
global archimedean/prime split of the explicit formula.  The point is narrower:
the one-sided finite-prime local kernel, with the `m = 0` diagonal removed, has
a negative one-dimensional quadratic-form value, so that isolated local piece
cannot itself be the positive semidefinite form supplied by a finite Hodge
realization.

This does not rule out a global semilocal Weil form, a missing-diagonal
archimedean/pole compensation mechanism, a spectral/cohomological realization,
or RH.  Evidence class: formal/certificate artifact and dead-end elimination.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace PrimeLocalHodgeNoGo

open PrimeLocalNoGo
open HodgeWeilBridge

universe u

/--
The one-point matrix whose single entry is the one-sided local prime kernel.

All prime/local rows are zero because this object is only a matrix container for
the closed-form local sign value; it is not the global CCM decomposition.
-/
noncomputable def onePointLocalData (r psi : ℝ) :
    CCMFiniteWeil.SemilocalFiniteWeilData PUnit PUnit ℝ where
  archBase := fun _ _ => oneSidedPrimeKernel r psi
  archTrace := fun _ _ => 0
  primeCoeff := fun _ => 0
  primeKernel := fun _ _ _ => 0

/-- The unique nonzero test vector on the one-point matrix. -/
def unitVector : PUnit -> ℝ :=
  fun _ => 1

/-- The single matrix entry is exactly the one-sided prime-local kernel. -/
theorem entry_onePointLocalData (r psi : ℝ) :
    CCMFiniteWeil.entry (onePointLocalData r psi) PUnit.unit PUnit.unit =
      oneSidedPrimeKernel r psi := by
  simp [onePointLocalData, CCMFiniteWeil.entry, CCMFiniteWeil.archPart,
    CCMFiniteWeil.primePart]

/-- The unit-vector quadratic form is exactly the one-sided prime-local kernel. -/
theorem quadraticForm_unitVector_onePointLocalData (r psi : ℝ) :
    quadraticForm (onePointLocalData r psi) unitVector =
      oneSidedPrimeKernel r psi := by
  simp [quadraticForm, unitVector, onePointLocalData, CCMFiniteWeil.entry,
    CCMFiniteWeil.archPart, CCMFiniteWeil.primePart]

/--
The one-sided local prime kernel supplies a negative vector for the one-point
finite semilocal matrix whenever `cos psi < r`.
-/
theorem hasNegativeVector_of_cos_lt {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi < r) :
    HasNegativeVector (onePointLocalData r psi) := by
  refine ⟨unitVector, ?_⟩
  rw [quadraticForm_unitVector_onePointLocalData]
  exact oneSidedPrimeKernel_neg_of_cos_lt hr0 hr1 hcos

/-- The one-point local matrix is not positive semidefinite when `cos psi < r`. -/
theorem not_positiveSemidefinite_of_cos_lt {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi < r) :
    ¬ PositiveSemidefinite (onePointLocalData r psi) :=
  not_positiveSemidefinite_of_hasNegativeVector
    (hasNegativeVector_of_cos_lt hr0 hr1 hcos)

/--
The one-point local matrix admits no finite Hodge realization when
`cos psi < r`.
-/
theorem not_nonempty_hodgeRealization_of_cos_lt {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi < r) :
    ¬ Nonempty (FiniteHodgeRealization.{u} (onePointLocalData r psi)) :=
  not_nonempty_hodgeRealization_of_hasNegativeVector
    (hasNegativeVector_of_cos_lt hr0 hr1 hcos)

/-- Packaged finite negative-direction falsifier for the one-point local matrix. -/
noncomputable def finiteHodgeWeilFalsifier_of_cos_lt {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi < r) :
    FiniteHodgeWeilFalsifier (ι := PUnit) (κ := PUnit) where
  data := onePointLocalData r psi
  vector := unitVector
  quadraticForm_lt_zero := by
    rw [quadraticForm_unitVector_onePointLocalData]
    exact oneSidedPrimeKernel_neg_of_cos_lt hr0 hr1 hcos

/-- At every zero of cosine, the one-point local matrix has a negative vector. -/
theorem hasNegativeVector_of_cos_eq_zero {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi = 0) :
    HasNegativeVector (onePointLocalData r psi) := by
  refine ⟨unitVector, ?_⟩
  rw [quadraticForm_unitVector_onePointLocalData]
  exact oneSidedPrimeKernel_neg_of_cos_eq_zero hr0 hr1 hcos

/-- At a zero of cosine, the one-point local matrix is not positive semidefinite. -/
theorem not_positiveSemidefinite_of_cos_eq_zero {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi = 0) :
    ¬ PositiveSemidefinite (onePointLocalData r psi) :=
  not_positiveSemidefinite_of_hasNegativeVector
    (hasNegativeVector_of_cos_eq_zero hr0 hr1 hcos)

/--
At a zero of cosine, the one-point local matrix admits no finite Hodge
realization.
-/
theorem not_nonempty_hodgeRealization_of_cos_eq_zero {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi = 0) :
    ¬ Nonempty (FiniteHodgeRealization.{u} (onePointLocalData r psi)) :=
  not_nonempty_hodgeRealization_of_hasNegativeVector
    (hasNegativeVector_of_cos_eq_zero hr0 hr1 hcos)

end PrimeLocalHodgeNoGo
end JensenLadder
