import JensenLadder.SpectralRealization

/-!
# Morse-index criterion interfaces for the spectral route

The CCM/Suzuki spectral line organizes the surviving open problem around an
integer condition:

```text
the number of negative directions is zero at every scale.
```

This module gives that condition two precise Lean-facing interfaces:

* `MorseIndexRHEquivalence`: the direct criterion shape
  `NoNegativeModes ↔ RiemannHypothesis`.
* `MorseIndexSpectralCriterion`: the stronger spectral-realization shape
  `NoNegativeModes ↔ Nonempty RiemannXiRegularSpectralRealization`.

The split matters.  The positivity/Morse operator and the spectral/momentum
operator are different objects in the current program map; a proof of the
former criterion should not be silently presented as a non-circular spectral
realization.

It does **not** prove that the zeta Weil forms satisfy the criterion, does not
construct the limiting operator, and does not prove RH.  The load-bearing
analytic task is to instantiate one of these criterion structures
non-circularly for the zeta/CCM/Suzuki family.  Numerical inertia rows are
falsifier screens and separator diagnostics only; they are not proof evidence.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace MorseCriterion

universe u

open SpectralRealization

/-- The zero-Morse-index condition for a family of finite or limiting Weil
forms: there are no negative modes at any scale. -/
def NoNegativeModes {Scale : Type u} (negativeIndex : Scale → ℕ) : Prop :=
  ∀ a : Scale, negativeIndex a = 0

/-- Nonnegativity of a supplied bottom/lowest-eigenvalue function at every
scale.  For a concrete Weil-form family, `bottom a` is intended to be the
bottom of the scale-`a` form. -/
def NonnegativeBottom {Scale : Type u} (bottom : Scale → ℝ) : Prop :=
  ∀ a : Scale, 0 ≤ bottom a

/-- Direct Lean-facing version of a Morse-index criterion for RH.

This is the wall-immune integer criterion shape: zero negative index at every
scale is exactly mathlib's `RiemannHypothesis`.  Supplying this structure for a
concrete zeta Weil-form family is the load-bearing analytic theorem; the
structure itself only records the interface. -/
structure MorseIndexRHEquivalence where
  Scale : Type u
  negativeIndex : Scale → ℕ
  riemannHypothesis_of_noNegativeModes :
    NoNegativeModes negativeIndex → RiemannHypothesis
  noNegativeModes_of_riemannHypothesis :
    RiemannHypothesis → NoNegativeModes negativeIndex

namespace MorseIndexRHEquivalence

/-- A direct Morse-index criterion identifies RH with zero negative index at
every scale. -/
theorem riemannHypothesis_iff_noNegativeModes
    (C : MorseIndexRHEquivalence.{u}) :
    RiemannHypothesis ↔ NoNegativeModes C.negativeIndex := by
  constructor
  · exact C.noNegativeModes_of_riemannHypothesis
  · exact C.riemannHypothesis_of_noNegativeModes

/-- Zero negative modes at every scale imply RH, once the direct Morse-index
criterion has been supplied. -/
theorem rh_of_noNegativeModes
    (C : MorseIndexRHEquivalence.{u})
    (h : NoNegativeModes C.negativeIndex) :
    RiemannHypothesis :=
  C.riemannHypothesis_of_noNegativeModes h

/-- RH implies zero negative modes at every scale for a supplied direct
Morse-index criterion. -/
theorem noNegativeModes_of_rh
    (C : MorseIndexRHEquivalence.{u})
    (hRH : RiemannHypothesis) :
    NoNegativeModes C.negativeIndex :=
  C.noNegativeModes_of_riemannHypothesis hRH

/-- A certified nonzero negative index at one scale refutes `NoNegativeModes`
for the direct criterion. -/
theorem not_noNegativeModes_of_negativeIndex_ne_zero
    (C : MorseIndexRHEquivalence.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ NoNegativeModes C.negativeIndex := by
  intro h
  exact ha (h a)

/-- Under a direct Morse-index criterion, a certified nonzero negative index at
one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_negativeIndex_ne_zero
    (C : MorseIndexRHEquivalence.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact not_noNegativeModes_of_negativeIndex_ne_zero C ha
    (C.noNegativeModes_of_riemannHypothesis hRH)

/-- Under a direct Morse-index criterion, a certified nonzero negative index
rules out the exact regular spectral-realization endpoint as well.

This is a consequence of the already-formalized equivalence between the regular
spectral endpoint and RH; it is not a separate spectral construction. -/
theorem not_regularSpectralRealization_of_negativeIndex_ne_zero
    (C : MorseIndexRHEquivalence.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} := by
  intro hS
  have hRH : RiemannHypothesis :=
    SpectralRealization.nonempty_regularSpectralRealization_iff_riemannHypothesis.1 hS
  exact not_riemannHypothesis_of_negativeIndex_ne_zero C ha hRH

end MorseIndexRHEquivalence

/-- Calibration between a bottom/lowest-eigenvalue function and the Morse index
for a supplied direct RH-equivalence criterion.

The field `index_zero_iff_bottom_nonneg` is a per-scale spectral-algebra input:
it records that the scale has no negative directions exactly when its bottom is
nonnegative.  This structure does not prove such a calibration for any concrete
operator; it is the Lean-facing place where finite matrix certificates or an
analytic min-max theorem enter the Morse route. -/
structure LowestEigenvalueCalibration (C : MorseIndexRHEquivalence.{u}) where
  bottom : C.Scale → ℝ
  index_zero_iff_bottom_nonneg :
    ∀ a : C.Scale, C.negativeIndex a = 0 ↔ 0 ≤ bottom a

namespace LowestEigenvalueCalibration

/-- Per-scale bottom/index calibration promotes to the global statement:
zero Morse index at every scale iff every bottom value is nonnegative. -/
theorem noNegativeModes_iff_nonnegativeBottom
    {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) :
    NoNegativeModes C.negativeIndex ↔ NonnegativeBottom B.bottom := by
  constructor
  · intro h a
    exact (B.index_zero_iff_bottom_nonneg a).1 (h a)
  · intro h a
    exact (B.index_zero_iff_bottom_nonneg a).2 (h a)

/-- A direct Morse criterion plus bottom/index calibration identifies RH with
nonnegativity of the bottom at every scale. -/
theorem riemannHypothesis_iff_nonnegativeBottom
    (C : MorseIndexRHEquivalence.{u})
    (B : LowestEigenvalueCalibration C) :
    RiemannHypothesis ↔ NonnegativeBottom B.bottom := by
  exact (MorseIndexRHEquivalence.riemannHypothesis_iff_noNegativeModes C).trans
    (noNegativeModes_iff_nonnegativeBottom B)

/-- RH implies nonnegative bottom at every scale under the calibrated direct
Morse criterion. -/
theorem nonnegativeBottom_of_riemannHypothesis
    (C : MorseIndexRHEquivalence.{u})
    (B : LowestEigenvalueCalibration C)
    (hRH : RiemannHypothesis) :
    NonnegativeBottom B.bottom :=
  (riemannHypothesis_iff_nonnegativeBottom C B).1 hRH

/-- Nonnegative bottom at every scale implies RH under the calibrated direct
Morse criterion. -/
theorem riemannHypothesis_of_nonnegativeBottom
    (C : MorseIndexRHEquivalence.{u})
    (B : LowestEigenvalueCalibration C)
    (hbottom : NonnegativeBottom B.bottom) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_nonnegativeBottom C B).2 hbottom

/-- A negative bottom value at one scale certifies a nonzero negative index at
that same scale. -/
theorem negativeIndex_ne_zero_of_bottom_lt
    {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) {a : C.Scale}
    (ha : B.bottom a < 0) :
    C.negativeIndex a ≠ 0 := by
  intro hzero
  have hnonneg : 0 ≤ B.bottom a := (B.index_zero_iff_bottom_nonneg a).1 hzero
  exact (not_le_of_gt ha) hnonneg

/-- A negative bottom value at one scale refutes global zero Morse index. -/
theorem not_noNegativeModes_of_bottom_lt
    {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) {a : C.Scale}
    (ha : B.bottom a < 0) :
    ¬ NoNegativeModes C.negativeIndex :=
  MorseIndexRHEquivalence.not_noNegativeModes_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_bottom_lt B ha)

/-- Under the calibrated direct Morse criterion, a negative bottom value at one
scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_bottom_lt
    {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) {a : C.Scale}
    (ha : B.bottom a < 0) :
    ¬ RiemannHypothesis :=
  MorseIndexRHEquivalence.not_riemannHypothesis_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_bottom_lt B ha)

/-- Under the calibrated direct Morse criterion, a negative bottom value at one
scale also rules out the exact regular spectral-realization endpoint. -/
theorem not_regularSpectralRealization_of_bottom_lt
    {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) {a : C.Scale}
    (ha : B.bottom a < 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} :=
  MorseIndexRHEquivalence.not_regularSpectralRealization_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_bottom_lt B ha)

end LowestEigenvalueCalibration

/-- Route-control metadata for a calibrated lowest eigenvalue: the bottom mode is
simple at each scale where `simpleBottom` holds.

This is the Lean-facing place for Bochner/simple-top-eigenvalue style genericity
conditions after translating them to the Morse bottom.  It deliberately carries
no sign information.  The RH-bearing row remains nonnegativity of the calibrated
bottom. -/
structure SimpleBottomCalibration {C : MorseIndexRHEquivalence.{u}}
    (B : LowestEigenvalueCalibration C) where
  simpleBottom : C.Scale → Prop

namespace SimpleBottomCalibration

/-- The calibrated bottom is simple at every scale. -/
def SimpleBottoms {C : MorseIndexRHEquivalence.{u}}
    {B : LowestEigenvalueCalibration C}
    (S : SimpleBottomCalibration B) : Prop :=
  ∀ a : C.Scale, S.simpleBottom a

/-- The calibrated bottom is simple at one specified scale. -/
def SimpleAt {C : MorseIndexRHEquivalence.{u}}
    {B : LowestEigenvalueCalibration C}
    (S : SimpleBottomCalibration B) (a : C.Scale) : Prop :=
  S.simpleBottom a

/-- Simplicity can be carried alongside the bottom nonnegativity row, but it does
not replace that sign row: RH still follows through `NonnegativeBottom`. -/
theorem riemannHypothesis_of_simpleBottoms_and_nonnegativeBottom
    {C : MorseIndexRHEquivalence.{u}} {B : LowestEigenvalueCalibration C}
    (S : SimpleBottomCalibration B)
    (_hsimple : SimpleBottoms S)
    (hbottom : NonnegativeBottom B.bottom) :
    RiemannHypothesis :=
  LowestEigenvalueCalibration.riemannHypothesis_of_nonnegativeBottom C B hbottom

/-- A simple bottom can still be negative.  Under the calibrated Morse/RH
criterion, a simple negative bottom at one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_simpleAt_and_bottom_lt
    {C : MorseIndexRHEquivalence.{u}} {B : LowestEigenvalueCalibration C}
    (S : SimpleBottomCalibration B) {a : C.Scale}
    (_hsimple : SimpleAt S a)
    (ha : B.bottom a < 0) :
    ¬ RiemannHypothesis :=
  LowestEigenvalueCalibration.not_riemannHypothesis_of_bottom_lt B ha

/-- A packaged certificate that carries both Bochner-style bottom simplicity and
the actual sign row needed by the calibrated Morse route. -/
structure SimpleBottomRHCertificate (C : MorseIndexRHEquivalence.{u}) where
  calibration : LowestEigenvalueCalibration C
  simplicity : SimpleBottomCalibration calibration
  simpleBottoms : SimpleBottoms simplicity
  bottom_nonnegative : NonnegativeBottom calibration.bottom

namespace SimpleBottomRHCertificate

/-- A simple-bottom certificate proves RH only because it includes the
nonnegative-bottom row. -/
theorem riemannHypothesis
    (C : MorseIndexRHEquivalence.{u})
    (cert : SimpleBottomRHCertificate C) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleBottoms_and_nonnegativeBottom
    cert.simplicity cert.simpleBottoms cert.bottom_nonnegative

end SimpleBottomRHCertificate

/-- A packaged simple-bottom falsifier.  The simplicity row is diagnostic; the
negative bottom value is the sign-bearing falsifier. -/
structure SimpleBottomFalsifier (C : MorseIndexRHEquivalence.{u}) where
  calibration : LowestEigenvalueCalibration C
  simplicity : SimpleBottomCalibration calibration
  scale : C.Scale
  simpleAt : SimpleAt simplicity scale
  bottom_lt_zero : calibration.bottom scale < 0

namespace SimpleBottomFalsifier

/-- A simple negative bottom refutes RH under the supplied calibrated Morse/RH
criterion. -/
theorem not_riemannHypothesis
    (C : MorseIndexRHEquivalence.{u})
    (cert : SimpleBottomFalsifier C) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_simpleAt_and_bottom_lt
    cert.simplicity cert.simpleAt cert.bottom_lt_zero

end SimpleBottomFalsifier

end SimpleBottomCalibration

/-- A supplied decomposition of the Morse index into odd-sector and even-sector
negative directions.

This is only sector bookkeeping.  It does not define the parity involution or
prove that a concrete Weil form decomposes this way.  It records the interface
needed for the odd-function criterion: if the even sector is protected from
negative directions, then the RH-bearing negative-index test can be read on the
odd sector alone.  Zero modes/kernels are not counted by this structure. -/
structure ParityMorseCalibration (C : MorseIndexRHEquivalence.{u}) where
  oddNegativeIndex : C.Scale → ℕ
  evenNegativeIndex : C.Scale → ℕ
  negativeIndex_eq :
    ∀ a : C.Scale, C.negativeIndex a = oddNegativeIndex a + evenNegativeIndex a

namespace ParityMorseCalibration

/-- There are no negative directions in the odd sector at any scale. -/
def NoOddNegativeModes {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) : Prop :=
  ∀ a : C.Scale, P.oddNegativeIndex a = 0

/-- The even sector is protected from negative directions at every scale.  This
allows even zero modes/kernels; it only excludes even *negative* modes. -/
def EvenSectorProtected {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) : Prop :=
  ∀ a : C.Scale, P.evenNegativeIndex a = 0

/-- A zero total negative index forces a zero odd-sector negative index at one
scale. -/
theorem oddNegativeIndex_eq_zero_of_negativeIndex_eq_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : C.negativeIndex a = 0) :
    P.oddNegativeIndex a = 0 := by
  have hsum : P.oddNegativeIndex a + P.evenNegativeIndex a = 0 := by
    rw [← P.negativeIndex_eq a, ha]
  exact Nat.eq_zero_of_add_eq_zero_right hsum

/-- A zero total negative index forces a zero even-sector negative index at one
scale. -/
theorem evenNegativeIndex_eq_zero_of_negativeIndex_eq_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : C.negativeIndex a = 0) :
    P.evenNegativeIndex a = 0 := by
  have hsum : P.oddNegativeIndex a + P.evenNegativeIndex a = 0 := by
    rw [← P.negativeIndex_eq a, ha]
  exact Nat.eq_zero_of_add_eq_zero_left hsum

/-- Global zero Morse index implies no odd negative modes. -/
theorem noOddNegativeModes_of_noNegativeModes
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C)
    (h : NoNegativeModes C.negativeIndex) :
    NoOddNegativeModes P := by
  intro a
  exact oddNegativeIndex_eq_zero_of_negativeIndex_eq_zero P (h a)

/-- Global zero Morse index implies the even sector is protected from negative
modes. -/
theorem evenSectorProtected_of_noNegativeModes
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C)
    (h : NoNegativeModes C.negativeIndex) :
    EvenSectorProtected P := by
  intro a
  exact evenNegativeIndex_eq_zero_of_negativeIndex_eq_zero P (h a)

/-- If both parity sectors have zero negative index at every scale, then the
global negative index is zero at every scale. -/
theorem noNegativeModes_of_noOddNegativeModes_of_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C)
    (hOdd : NoOddNegativeModes P)
    (hEven : EvenSectorProtected P) :
    NoNegativeModes C.negativeIndex := by
  intro a
  rw [P.negativeIndex_eq a, hOdd a, hEven a]

/-- Global absence of negative modes is exactly the conjunction of the two
parity-sector rows: no odd negative modes and no even negative modes.

This records that even-sector protection is a genuine row of the criterion, not
a consequence of the odd-sector condition. -/
theorem noNegativeModes_iff_noOddNegativeModes_and_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) :
    NoNegativeModes C.negativeIndex ↔ NoOddNegativeModes P ∧ EvenSectorProtected P := by
  constructor
  · intro h
    exact ⟨noOddNegativeModes_of_noNegativeModes P h, evenSectorProtected_of_noNegativeModes P h⟩
  · intro h
    exact noNegativeModes_of_noOddNegativeModes_of_evenSectorProtected P h.1 h.2

/-- Under a direct Morse/RH criterion, RH is equivalent to the two parity-sector
rows together.  The even-sector row is explicit and is not discharged by the
odd-sector row. -/
theorem riemannHypothesis_iff_noOddNegativeModes_and_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) :
    RiemannHypothesis ↔ NoOddNegativeModes P ∧ EvenSectorProtected P := by
  exact (MorseIndexRHEquivalence.riemannHypothesis_iff_noNegativeModes C).trans
    (noNegativeModes_iff_noOddNegativeModes_and_evenSectorProtected P)

/-- When the even sector is protected from negative directions, global zero
Morse index is equivalent to zero odd-sector negative index. -/
theorem noNegativeModes_iff_noOddNegativeModes_of_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C)
    (hEven : EvenSectorProtected P) :
    NoNegativeModes C.negativeIndex ↔ NoOddNegativeModes P := by
  constructor
  · exact noOddNegativeModes_of_noNegativeModes P
  · intro hOdd
    exact noNegativeModes_of_noOddNegativeModes_of_evenSectorProtected P hOdd hEven

/-- Under a direct Morse/RH criterion, if the even sector is protected then RH is
equivalent to the absence of odd negative modes. -/
theorem riemannHypothesis_iff_noOddNegativeModes_of_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C)
    (hEven : EvenSectorProtected P) :
    RiemannHypothesis ↔ NoOddNegativeModes P := by
  exact (MorseIndexRHEquivalence.riemannHypothesis_iff_noNegativeModes C).trans
    (noNegativeModes_iff_noOddNegativeModes_of_evenSectorProtected P hEven)

/-- A nonzero odd-sector negative index at one scale certifies a nonzero global
negative index at that scale. -/
theorem negativeIndex_ne_zero_of_oddNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.oddNegativeIndex a ≠ 0) :
    C.negativeIndex a ≠ 0 := by
  intro htotal
  exact ha (oddNegativeIndex_eq_zero_of_negativeIndex_eq_zero P htotal)

/-- A nonzero even-sector negative index at one scale certifies a nonzero global
negative index at that scale. -/
theorem negativeIndex_ne_zero_of_evenNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.evenNegativeIndex a ≠ 0) :
    C.negativeIndex a ≠ 0 := by
  intro htotal
  exact ha (evenNegativeIndex_eq_zero_of_negativeIndex_eq_zero P htotal)

/-- Under a direct Morse/RH criterion, a nonzero odd-sector negative index at
one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_oddNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.oddNegativeIndex a ≠ 0) :
    ¬ RiemannHypothesis :=
  MorseIndexRHEquivalence.not_riemannHypothesis_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_oddNegativeIndex_ne_zero P ha)

/-- Under a direct Morse/RH criterion, a nonzero even-sector negative index at
one scale is an RH falsifier.  Even zero modes are allowed; even negative modes
are not. -/
theorem not_riemannHypothesis_of_evenNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.evenNegativeIndex a ≠ 0) :
    ¬ RiemannHypothesis :=
  MorseIndexRHEquivalence.not_riemannHypothesis_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_evenNegativeIndex_ne_zero P ha)

/-- Under a direct Morse/RH criterion, a nonzero odd-sector negative index also
rules out the exact regular spectral-realization endpoint. -/
theorem not_regularSpectralRealization_of_oddNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.oddNegativeIndex a ≠ 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} :=
  MorseIndexRHEquivalence.not_regularSpectralRealization_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_oddNegativeIndex_ne_zero P ha)

/-- Under a direct Morse/RH criterion, a nonzero even-sector negative index also
rules out the exact regular spectral-realization endpoint. -/
theorem not_regularSpectralRealization_of_evenNegativeIndex_ne_zero
    {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) {a : C.Scale}
    (ha : P.evenNegativeIndex a ≠ 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} :=
  MorseIndexRHEquivalence.not_regularSpectralRealization_of_negativeIndex_ne_zero C
    (negativeIndex_ne_zero_of_evenNegativeIndex_ne_zero P ha)

/-- Nonnegativity of a supplied odd-sector bottom at every scale.

This is the odd-sector analogue of `NonnegativeBottom`.  It records the
no-negative-direction boundary for the odd sector; strict positivity of a
concrete quadratic form on nonzero odd functions is a stronger analytic input
and is not asserted by this bookkeeping predicate. -/
def NonnegativeOddBottom {C : MorseIndexRHEquivalence.{u}}
    (_P : ParityMorseCalibration C) (oddBottom : C.Scale → ℝ) : Prop :=
  ∀ a : C.Scale, 0 ≤ oddBottom a

/-- Nonnegativity of a supplied even-sector bottom at every scale.

This records the even-sector protection row in bottom/eigenvalue form.  Supplying
the bottom and its min-max calibration is analytic input; the predicate itself
does not prove even-sector protection for a concrete zeta family. -/
def NonnegativeEvenBottom {C : MorseIndexRHEquivalence.{u}}
    (_P : ParityMorseCalibration C) (evenBottom : C.Scale → ℝ) : Prop :=
  ∀ a : C.Scale, 0 ≤ evenBottom a

/-- Calibration between an odd-sector bottom/lowest-eigenvalue function and the
odd-sector Morse index.

The field `odd_index_zero_iff_bottom_nonneg` is the odd-sector min-max input:
there is no odd negative direction at scale `a` exactly when the supplied
odd-sector bottom is nonnegative.  Supplying this for a concrete Weil-form
family is analytic work; this structure only records the Lean-facing interface. -/
structure OddLowestEigenvalueCalibration {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) where
  oddBottom : C.Scale → ℝ
  odd_index_zero_iff_bottom_nonneg :
    ∀ a : C.Scale, P.oddNegativeIndex a = 0 ↔ 0 ≤ oddBottom a

/-- Calibration between an even-sector bottom/lowest-eigenvalue function and the
even-sector Morse index.

The field `even_index_zero_iff_bottom_nonneg` is the even-sector min-max input:
there is no even negative direction at scale `a` exactly when the supplied
even-sector bottom is nonnegative.  This is the quantitative form of
`EvenSectorProtected`; it is still an analytic obligation when instantiated for
a concrete Weil-form family. -/
structure EvenLowestEigenvalueCalibration {C : MorseIndexRHEquivalence.{u}}
    (P : ParityMorseCalibration C) where
  evenBottom : C.Scale → ℝ
  even_index_zero_iff_bottom_nonneg :
    ∀ a : C.Scale, P.evenNegativeIndex a = 0 ↔ 0 ≤ evenBottom a

namespace OddLowestEigenvalueCalibration

/-- Odd-sector bottom/index calibration promotes to the global odd-sector
statement: no odd negative modes iff the odd-sector bottom is nonnegative at
every scale. -/
theorem noOddNegativeModes_iff_nonnegativeOddBottom
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) :
    NoOddNegativeModes P ↔ NonnegativeOddBottom P O.oddBottom := by
  constructor
  · intro h a
    exact (O.odd_index_zero_iff_bottom_nonneg a).1 (h a)
  · intro h a
    exact (O.odd_index_zero_iff_bottom_nonneg a).2 (h a)

/-- If the even sector has no negative directions, then the calibrated
odd-sector bottom is equivalent to global zero Morse index. -/
theorem noNegativeModes_iff_nonnegativeOddBottom_of_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P)
    (hEven : EvenSectorProtected P) :
    NoNegativeModes C.negativeIndex ↔ NonnegativeOddBottom P O.oddBottom := by
  exact (noNegativeModes_iff_noOddNegativeModes_of_evenSectorProtected P hEven).trans
    (noOddNegativeModes_iff_nonnegativeOddBottom O)

/-- Under a direct Morse/RH criterion and even-sector protection, RH is
equivalent to nonnegativity of the calibrated odd-sector bottom at every scale. -/
theorem riemannHypothesis_iff_nonnegativeOddBottom_of_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P)
    (hEven : EvenSectorProtected P) :
    RiemannHypothesis ↔ NonnegativeOddBottom P O.oddBottom := by
  exact (riemannHypothesis_iff_noOddNegativeModes_of_evenSectorProtected P hEven).trans
    (noOddNegativeModes_iff_nonnegativeOddBottom O)

/-- Calibrated parity split: under a direct Morse/RH criterion, RH is equivalent
to the conjunction of odd-sector bottom nonnegativity and even-sector protection.

This is the version that keeps the even-sector obligation visible instead of
burying it as a side hypothesis. -/
theorem riemannHypothesis_iff_nonnegativeOddBottom_and_evenSectorProtected
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) :
    RiemannHypothesis ↔ NonnegativeOddBottom P O.oddBottom ∧ EvenSectorProtected P := by
  constructor
  · intro hRH
    have hsplit :=
      (riemannHypothesis_iff_noOddNegativeModes_and_evenSectorProtected P).1 hRH
    exact ⟨(noOddNegativeModes_iff_nonnegativeOddBottom O).1 hsplit.1, hsplit.2⟩
  · intro h
    have hsplit : NoOddNegativeModes P ∧ EvenSectorProtected P :=
      ⟨(noOddNegativeModes_iff_nonnegativeOddBottom O).2 h.1, h.2⟩
    exact (riemannHypothesis_iff_noOddNegativeModes_and_evenSectorProtected P).2 hsplit

/-- A negative odd-sector bottom value at one scale certifies a nonzero
odd-sector negative index at that scale. -/
theorem oddNegativeIndex_ne_zero_of_oddBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : O.oddBottom a < 0) :
    P.oddNegativeIndex a ≠ 0 := by
  intro hzero
  have hnonneg : 0 ≤ O.oddBottom a :=
    (O.odd_index_zero_iff_bottom_nonneg a).1 hzero
  exact (not_le_of_gt ha) hnonneg

/-- A negative odd-sector bottom value at one scale refutes global absence of
odd negative modes. -/
theorem not_noOddNegativeModes_of_oddBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : O.oddBottom a < 0) :
    ¬ NoOddNegativeModes P := by
  intro h
  exact oddNegativeIndex_ne_zero_of_oddBottom_lt O ha (h a)

/-- Under a direct Morse/RH criterion, a negative calibrated odd-sector bottom
at one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_oddBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : O.oddBottom a < 0) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_oddNegativeIndex_ne_zero P
    (oddNegativeIndex_ne_zero_of_oddBottom_lt O ha)

/-- Under a direct Morse/RH criterion, a negative calibrated odd-sector bottom
also rules out the exact regular spectral-realization endpoint. -/
theorem not_regularSpectralRealization_of_oddBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : O.oddBottom a < 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} :=
  not_regularSpectralRealization_of_oddNegativeIndex_ne_zero P
    (oddNegativeIndex_ne_zero_of_oddBottom_lt O ha)

end OddLowestEigenvalueCalibration

namespace EvenLowestEigenvalueCalibration

/-- Even-sector bottom/index calibration is exactly even-sector protection. -/
theorem evenSectorProtected_iff_nonnegativeEvenBottom
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (E : EvenLowestEigenvalueCalibration P) :
    EvenSectorProtected P ↔ NonnegativeEvenBottom P E.evenBottom := by
  constructor
  · intro h a
    exact (E.even_index_zero_iff_bottom_nonneg a).1 (h a)
  · intro h a
    exact (E.even_index_zero_iff_bottom_nonneg a).2 (h a)

/-- A negative even-sector bottom value at one scale certifies a nonzero
even-sector negative index at that scale. -/
theorem evenNegativeIndex_ne_zero_of_evenBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (E : EvenLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : E.evenBottom a < 0) :
    P.evenNegativeIndex a ≠ 0 := by
  intro hzero
  have hnonneg : 0 ≤ E.evenBottom a :=
    (E.even_index_zero_iff_bottom_nonneg a).1 hzero
  exact (not_le_of_gt ha) hnonneg

/-- A negative even-sector bottom value at one scale refutes even-sector
protection. -/
theorem not_evenSectorProtected_of_evenBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (E : EvenLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : E.evenBottom a < 0) :
    ¬ EvenSectorProtected P := by
  intro h
  exact evenNegativeIndex_ne_zero_of_evenBottom_lt E ha (h a)

/-- Under a direct Morse/RH criterion, a negative calibrated even-sector bottom
at one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_evenBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (E : EvenLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : E.evenBottom a < 0) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_evenNegativeIndex_ne_zero P
    (evenNegativeIndex_ne_zero_of_evenBottom_lt E ha)

/-- Under a direct Morse/RH criterion, a negative calibrated even-sector bottom
also rules out the exact regular spectral-realization endpoint. -/
theorem not_regularSpectralRealization_of_evenBottom_lt
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (E : EvenLowestEigenvalueCalibration P) {a : C.Scale}
    (ha : E.evenBottom a < 0) :
    ¬ Nonempty RiemannXiRegularSpectralRealization.{0} :=
  not_regularSpectralRealization_of_evenNegativeIndex_ne_zero P
    (evenNegativeIndex_ne_zero_of_evenBottom_lt E ha)

end EvenLowestEigenvalueCalibration

namespace OddLowestEigenvalueCalibration

/-- Fully calibrated parity-bottom criterion: under a direct Morse/RH criterion,
RH is equivalent to nonnegativity of both the odd-sector and even-sector
calibrated bottoms at every scale.

This theorem exposes both analytic rows.  It does not supply either calibration
for a concrete zeta family. -/
theorem riemannHypothesis_iff_nonnegativeOddBottom_and_nonnegativeEvenBottom
    {C : MorseIndexRHEquivalence.{u}} {P : ParityMorseCalibration C}
    (O : OddLowestEigenvalueCalibration P)
    (E : EvenLowestEigenvalueCalibration P) :
    RiemannHypothesis ↔
      NonnegativeOddBottom P O.oddBottom ∧ NonnegativeEvenBottom P E.evenBottom := by
  constructor
  · intro hRH
    have hsplit :=
      (riemannHypothesis_iff_nonnegativeOddBottom_and_evenSectorProtected O).1 hRH
    exact ⟨hsplit.1,
      (EvenLowestEigenvalueCalibration.evenSectorProtected_iff_nonnegativeEvenBottom E).1
        hsplit.2⟩
  · intro h
    have hsplit : NonnegativeOddBottom P O.oddBottom ∧ EvenSectorProtected P :=
      ⟨h.1,
        (EvenLowestEigenvalueCalibration.evenSectorProtected_iff_nonnegativeEvenBottom E).2
          h.2⟩
    exact (riemannHypothesis_iff_nonnegativeOddBottom_and_evenSectorProtected O).2 hsplit

end OddLowestEigenvalueCalibration

end ParityMorseCalibration

/-- A Lean-facing version of a Morse-index criterion for RH.

The field `negativeIndex` abstracts the number of negative directions at scale
`a`.  The forward map is the analytic spectral-identification theorem: zero
negative index at every scale must produce the exact regular `Ξ` spectral
realization.  The reverse map records the converse calibration.  The criterion
is useful as a proof route only when these maps are constructed independently of
the `Ξ` zero set. -/
structure MorseIndexSpectralCriterion where
  Scale : Type u
  negativeIndex : Scale → ℕ
  realization_of_noNegativeModes :
    NoNegativeModes negativeIndex → RiemannXiRegularSpectralRealization.{0}
  noNegativeModes_of_realization :
    RiemannXiRegularSpectralRealization.{0} → NoNegativeModes negativeIndex

namespace MorseIndexRHEquivalence

/-- A direct RH-equivalence criterion canonically induces the stronger spectral
criterion by passing through the tautological RH-to-regular-zero-set realization.

This is a calibration bridge, not a non-circular Hilbert--Pólya construction:
the forward map first proves RH from `NoNegativeModes`, then uses the canonical
regular zero-set realization from `SpectralRealization`. -/
noncomputable def toSpectralCriterion
    (C : MorseIndexRHEquivalence.{u}) :
    MorseIndexSpectralCriterion.{u} where
  Scale := C.Scale
  negativeIndex := C.negativeIndex
  realization_of_noNegativeModes := by
    intro h
    exact SpectralRealization.canonicalRegularSpectralRealizationOfRegularXiZerosReal
      ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
        (C.riemannHypothesis_of_noNegativeModes h))
  noNegativeModes_of_realization := by
    intro S
    exact C.noNegativeModes_of_riemannHypothesis
      (SpectralRealization.riemannHypothesis_of_regularSpectralRealization S)

end MorseIndexRHEquivalence

/-- The criterion identifies zero Morse index with existence of the exact
regular spectral realization. -/
theorem noNegativeModes_iff_regularSpectralRealization
    (C : MorseIndexSpectralCriterion.{u}) :
    NoNegativeModes C.negativeIndex ↔ Nonempty RiemannXiRegularSpectralRealization.{0} := by
  constructor
  · intro h
    exact ⟨C.realization_of_noNegativeModes h⟩
  · rintro ⟨S⟩
    exact C.noNegativeModes_of_realization S

/-- Under a Morse-index spectral criterion, mathlib's RH is equivalent to zero
negative Morse index at every scale. -/
theorem riemannHypothesis_iff_noNegativeModes
    (C : MorseIndexSpectralCriterion.{u}) :
    RiemannHypothesis ↔ NoNegativeModes C.negativeIndex := by
  exact SpectralRealization.nonempty_regularSpectralRealization_iff_riemannHypothesis.symm.trans
    (noNegativeModes_iff_regularSpectralRealization C).symm

/-- Zero negative modes at every scale imply RH, once the Morse-index spectral
criterion has been supplied. -/
theorem riemannHypothesis_of_noNegativeModes
    (C : MorseIndexSpectralCriterion.{u})
    (h : NoNegativeModes C.negativeIndex) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_noNegativeModes C).2 h

/-- RH implies zero negative modes at every scale for any supplied Morse-index
spectral criterion. -/
theorem noNegativeModes_of_riemannHypothesis
    (C : MorseIndexSpectralCriterion.{u})
    (hRH : RiemannHypothesis) :
    NoNegativeModes C.negativeIndex :=
  (riemannHypothesis_iff_noNegativeModes C).1 hRH

/-- A certified nonzero negative index at one scale refutes `NoNegativeModes`. -/
theorem not_noNegativeModes_of_negativeIndex_ne_zero
    (C : MorseIndexSpectralCriterion.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ NoNegativeModes C.negativeIndex := by
  intro h
  exact ha (h a)

/-- Under a supplied Morse-index spectral criterion, a certified nonzero
negative index at one scale is an RH falsifier. -/
theorem not_riemannHypothesis_of_negativeIndex_ne_zero
    (C : MorseIndexSpectralCriterion.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact not_noNegativeModes_of_negativeIndex_ne_zero C ha
    (noNegativeModes_of_riemannHypothesis C hRH)

/-- A packaged finite or limiting negative-mode certificate for a criterion. -/
structure CertifiedNegativeMode (C : MorseIndexSpectralCriterion.{u}) where
  scale : C.Scale
  negativeIndex_ne_zero : C.negativeIndex scale ≠ 0

/-- A packaged negative-mode certificate is an RH falsifier under the supplied
Morse-index spectral criterion. -/
theorem not_riemannHypothesis_of_certifiedNegativeMode
    (C : MorseIndexSpectralCriterion.{u})
    (cert : CertifiedNegativeMode C) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_negativeIndex_ne_zero C cert.negativeIndex_ne_zero

end MorseCriterion
end JensenLadder
