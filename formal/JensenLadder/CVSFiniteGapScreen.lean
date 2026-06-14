import JensenLadder.CVSGapPreservation
import Mathlib.Tactic

/-!
# Finite interval gap screen for the C-vS route

This module records the certificate-facing algebra for deciding whether a
finite semilocal Weil operator has a genuinely resolved bottom-to-second gap.

The intended numerical/interval workflow is:

```text
exactBottom ∈ [reportedBottom - tolerance, reportedBottom + tolerance]
exactSecond ∈ [reportedSecond - tolerance, reportedSecond + tolerance]
2 * tolerance < reportedSecond - reportedBottom
---------------------------------------------------------------
0 < exactSecond - exactBottom
```

That conclusion is still only a finite spectral-screen row.  A concrete
operator family must separately prove that `exactBottom` and `exactSecond` are
the actual bottom and second spectral levels, that a positive gap gives the
simple-even C-vS hypothesis, and that the approximants converge to `Xi`.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CVSFiniteGapScreen

open CVSSpectralRoute
open CVSGapPreservation

universe u

/-- One finite two-level interval certificate.

The `reported*` values are the numerical centers, `tolerance` is a common
two-sided error radius, and `exact*` are the exact scalar levels being certified.
-/
structure TwoLevelIntervalCertificate where
  exactBottom : ℝ
  exactSecond : ℝ
  reportedBottom : ℝ
  reportedSecond : ℝ
  tolerance : ℝ
  tolerance_nonneg : 0 ≤ tolerance
  bottom_lower : reportedBottom - tolerance ≤ exactBottom
  bottom_upper : exactBottom ≤ reportedBottom + tolerance
  second_lower : reportedSecond - tolerance ≤ exactSecond
  second_upper : exactSecond ≤ reportedSecond + tolerance

namespace TwoLevelIntervalCertificate

/-- Exact bottom-to-second gap. -/
def exactGap (C : TwoLevelIntervalCertificate) : ℝ :=
  C.exactSecond - C.exactBottom

/-- Reported bottom-to-second gap before accounting for the tolerance radius. -/
def reportedGap (C : TwoLevelIntervalCertificate) : ℝ :=
  C.reportedSecond - C.reportedBottom

/-- The resolved-gap condition: the reported separation beats both endpoint
tolerances. -/
def GapResolved (C : TwoLevelIntervalCertificate) : Prop :=
  2 * C.tolerance < C.reportedGap

/-- Interval enclosures give a lower bound for the exact gap. -/
theorem reportedGap_sub_two_tolerance_le_exactGap
    (C : TwoLevelIntervalCertificate) :
    C.reportedGap - 2 * C.tolerance ≤ C.exactGap := by
  unfold reportedGap exactGap
  linarith [C.bottom_upper, C.second_lower]

/-- A resolved interval gap is an exact positive gap. -/
theorem exactGap_pos_of_gapResolved
    (C : TwoLevelIntervalCertificate)
    (hresolved : C.GapResolved) :
    0 < C.exactGap := by
  have hlower := C.reportedGap_sub_two_tolerance_le_exactGap
  have hpositive : 0 < C.reportedGap - 2 * C.tolerance := by
    dsimp [GapResolved] at hresolved
    linarith
  exact lt_of_lt_of_le hpositive hlower

/-- Failure of exact positive gap forces failure of the resolved interval row. -/
theorem not_gapResolved_of_exactGap_nonpos
    (C : TwoLevelIntervalCertificate)
    (hgap : C.exactGap ≤ 0) :
    ¬ C.GapResolved := by
  intro hresolved
  exact not_lt_of_ge hgap (C.exactGap_pos_of_gapResolved hresolved)

end TwoLevelIntervalCertificate

/-- Scale-indexed two-level interval certificates for a finite approximant
family. -/
structure ScaleTwoLevelIntervalCertificate (Scale : Type u) where
  exactBottom : Scale → ℝ
  exactSecond : Scale → ℝ
  reportedBottom : Scale → ℝ
  reportedSecond : Scale → ℝ
  tolerance : Scale → ℝ
  tolerance_nonneg : ∀ a : Scale, 0 ≤ tolerance a
  bottom_lower :
    ∀ a : Scale, reportedBottom a - tolerance a ≤ exactBottom a
  bottom_upper :
    ∀ a : Scale, exactBottom a ≤ reportedBottom a + tolerance a
  second_lower :
    ∀ a : Scale, reportedSecond a - tolerance a ≤ exactSecond a
  second_upper :
    ∀ a : Scale, exactSecond a ≤ reportedSecond a + tolerance a

namespace ScaleTwoLevelIntervalCertificate

/-- Exact scale-indexed bottom-to-second gap. -/
def exactGap {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale)
    (a : Scale) : ℝ :=
  C.exactSecond a - C.exactBottom a

/-- Reported scale-indexed bottom-to-second gap before tolerance. -/
def reportedGap {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale)
    (a : Scale) : ℝ :=
  C.reportedSecond a - C.reportedBottom a

/-- Pointwise resolved-gap condition for a scale-indexed certificate. -/
def GapResolved {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale) : Prop :=
  ∀ a : Scale, 2 * C.tolerance a < C.reportedGap a

/-- Extract the one-scale interval certificate at scale `a`. -/
def toSingle {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale)
    (a : Scale) :
    TwoLevelIntervalCertificate where
  exactBottom := C.exactBottom a
  exactSecond := C.exactSecond a
  reportedBottom := C.reportedBottom a
  reportedSecond := C.reportedSecond a
  tolerance := C.tolerance a
  tolerance_nonneg := C.tolerance_nonneg a
  bottom_lower := C.bottom_lower a
  bottom_upper := C.bottom_upper a
  second_lower := C.second_lower a
  second_upper := C.second_upper a

/-- Interval enclosures give a pointwise lower bound for the exact gap. -/
theorem reportedGap_sub_two_tolerance_le_exactGap
    {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale)
    (a : Scale) :
    C.reportedGap a - 2 * C.tolerance a ≤ C.exactGap a := by
  simpa [reportedGap, exactGap, toSingle,
    TwoLevelIntervalCertificate.reportedGap, TwoLevelIntervalCertificate.exactGap]
    using (C.toSingle a).reportedGap_sub_two_tolerance_le_exactGap

/-- Resolved gaps give a positive exact gap at every scale. -/
theorem positiveGap_of_gapResolved
    {Scale : Type u}
    (C : ScaleTwoLevelIntervalCertificate Scale)
    (hresolved : C.GapResolved) :
    PositiveGap C.exactGap := by
  intro a
  have hsingle : (C.toSingle a).GapResolved := by
    simpa [GapResolved, reportedGap, toSingle,
      TwoLevelIntervalCertificate.GapResolved,
      TwoLevelIntervalCertificate.reportedGap]
      using hresolved a
  simpa [exactGap, toSingle, TwoLevelIntervalCertificate.exactGap]
    using (C.toSingle a).exactGap_pos_of_gapResolved hsingle

/-- A resolved interval screen supplies the finite simple-even C-vS hypothesis
once the exact gap is calibrated to the ground-state gap. -/
theorem simpleEvenGroundStates_of_gapResolved
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (gapData : GroundStateGapData G)
    (C : ScaleTwoLevelIntervalCertificate A.Scale)
    (hgap : ∀ a : A.Scale, gapData.gap a = C.exactGap a)
    (hresolved : C.GapResolved) :
    SimpleEvenGroundStates G := by
  apply simpleEvenGroundStates_of_positiveGap gapData
  intro a
  rw [hgap a]
  exact C.positiveGap_of_gapResolved hresolved a

/-- Interval-resolved finite gaps plus the C-vS convergence row prove RH through
the existing spectral route. -/
theorem riemannHypothesis_of_gapResolved_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (gapData : GroundStateGapData G)
    (C : ScaleTwoLevelIntervalCertificate A.Scale)
    (hgap : ∀ a : A.Scale, gapData.gap a = C.exactGap a)
    (hresolved : C.GapResolved)
    (hconv : H.convergesToXi) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence G H
    (C.simpleEvenGroundStates_of_gapResolved gapData hgap hresolved) hconv

/-- Under the convergence row, a non-real regular `Xi` zero rules out the
resolved finite interval screen. -/
theorem not_gapResolved_of_nonrealRegularXiZero_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (gapData : GroundStateGapData G)
    (C : ScaleTwoLevelIntervalCertificate A.Scale)
    (hgap : ∀ a : A.Scale, gapData.gap a = C.exactGap a)
    (hconv : H.convergesToXi)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.GapResolved := by
  intro hresolved
  exact not_convergence_of_nonrealRegularXiZero_and_simpleEvenGroundStates
    G H (C.simpleEvenGroundStates_of_gapResolved gapData hgap hresolved)
    hz hzim hconv

end ScaleTwoLevelIntervalCertificate

/-- Packaged C-vS certificate using finite interval gap screens. -/
structure IntervalGapRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  gapData : GroundStateGapData groundStateData
  intervalData : ScaleTwoLevelIntervalCertificate approximants.Scale
  gap_eq :
    ∀ a : approximants.Scale,
      gapData.gap a = intervalData.exactGap a
  gapResolved : intervalData.GapResolved
  convergesToXi : convergence.convergesToXi

namespace IntervalGapRHCertificate

/-- A packaged interval-gap C-vS certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : IntervalGapRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.intervalData.riemannHypothesis_of_gapResolved_and_convergence
    cert.groundStateData cert.convergence cert.gapData
    cert.gap_eq cert.gapResolved cert.convergesToXi

end IntervalGapRHCertificate

end CVSFiniteGapScreen
end JensenLadder
