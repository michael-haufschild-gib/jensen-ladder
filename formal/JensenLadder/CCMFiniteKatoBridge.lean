import JensenLadder.CCMFrobeniusBound
import JensenLadder.CVSKatoWeyl
import Mathlib.Tactic

/-!
# Finite CCM Frobenius certificates as Kato radii

This module connects the finite CCM prime-perturbation certificate to the
unsquared radius used by the C-vS Kato/Weyl gap row.

The finite algebra proved here is:

```text
decomposedFrobeniusSq(P) <= r^2,  0 <= r
------------------------------------------------
||P v||_2^2 <= r^2 ||v||_2^2.
```

It also packages a scale-indexed CCM prime family into the two-level
`CVSKatoWeyl` route.  The hard analytic rows remain explicit: a concrete
operator family must still prove that this `l²` radius gives the bottom/second
eigenvalue deviation bounds, and must prove convergence to `Xi`.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMFiniteKatoBridge

open CCMFiniteWeil
open CCMFrobeniusBound
open CVSKatoWeyl
open CVSSpectralRoute

universe u

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Unsquared finite `l²` operator-radius bound for a CCM prime perturbation. -/
def L2OperatorRadiusBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radius : ℝ) : Prop :=
  0 ≤ radius ∧
    ∀ v : ι → ℝ,
      sqNorm (CCMPerturbationBound.primeOperator D v) ≤
        radius ^ 2 * sqNorm v

/-- Frobenius-square control by an unsquared radius. -/
def FrobeniusRadiusBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radius : ℝ) : Prop :=
  0 ≤ radius ∧ FrobeniusSqBound D (radius ^ 2)

/-- Decomposed local-row Frobenius-square control by an unsquared radius. -/
def DecomposedFrobeniusRadiusBound
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (radius : ℝ) : Prop :=
  0 ≤ radius ∧ DecomposedFrobeniusSqBound D (radius ^ 2)

/-- A Frobenius-square radius supplies the corresponding finite `l²`
operator-radius bound. -/
theorem l2OperatorRadiusBound_of_frobeniusRadiusBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radius : ℝ}
    (hbound : FrobeniusRadiusBound D radius) :
    L2OperatorRadiusBound D radius := by
  refine ⟨hbound.1, ?_⟩
  exact l2SqOperatorBound_of_frobeniusSqBound hbound.2

/-- A decomposed Frobenius certificate supplies the corresponding finite `l²`
operator-radius bound. -/
theorem l2OperatorRadiusBound_of_decomposedFrobeniusRadiusBound
    {D : SemilocalFiniteWeilData ι κ ℝ}
    {radius : ℝ}
    (hbound : DecomposedFrobeniusRadiusBound D radius) :
    L2OperatorRadiusBound D radius := by
  refine ⟨hbound.1, ?_⟩
  exact l2SqOperatorBound_of_decomposedFrobeniusSqBound hbound.2

/-- A scale-indexed finite CCM prime perturbation with a decomposed Frobenius
certificate radius at each scale. -/
structure ScaleCCMPrimePerturbation
    (Scale : Type u)
    (ι κ : Type*) [Fintype ι] [Fintype κ] where
  operatorData : Scale → SemilocalFiniteWeilData ι κ ℝ
  radius : Scale → ℝ
  radius_nonneg : ∀ a : Scale, 0 ≤ radius a
  decomposedFrobenius_bound :
    ∀ a : Scale,
      DecomposedFrobeniusSqBound (operatorData a) ((radius a) ^ 2)

namespace ScaleCCMPrimePerturbation

/-- Each finite CCM scale supplies a finite `l²` operator-radius bound. -/
theorem l2OperatorRadiusBound
    {Scale : Type u}
    (F : ScaleCCMPrimePerturbation Scale ι κ)
    (a : Scale) :
    L2OperatorRadiusBound (F.operatorData a) (F.radius a) :=
  l2OperatorRadiusBound_of_decomposedFrobeniusRadiusBound
    ⟨F.radius_nonneg a, F.decomposedFrobenius_bound a⟩

end ScaleCCMPrimePerturbation

/--
Scale-indexed CCM finite data plus the two eigenvalue-deviation rows needed by
the C-vS gap route.

The fields `bottom_upper` and `second_lower` are the analytic min-max/Weyl rows:
they are not derived from the finite Frobenius radius in this file.
-/
structure CCMKatoWeylData
    (Scale : Type u)
    (ι κ : Type*) [Fintype ι] [Fintype κ] where
  primeFamily : ScaleCCMPrimePerturbation Scale ι κ
  baseBottom : Scale → ℝ
  baseSecond : Scale → ℝ
  perturbedBottom : Scale → ℝ
  perturbedSecond : Scale → ℝ
  bottom_upper :
    ∀ a : Scale,
      perturbedBottom a ≤ baseBottom a + primeFamily.radius a
  second_lower :
    ∀ a : Scale,
      baseSecond a - primeFamily.radius a ≤ perturbedSecond a

namespace CCMKatoWeylData

/-- Forget the CCM matrix data to the two-level Kato/Weyl data consumed by the
C-vS gap algebra. -/
def toScaleTwoLevelDeviation
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ) :
    ScaleTwoLevelDeviation Scale where
  baseBottom := D.baseBottom
  baseSecond := D.baseSecond
  perturbedBottom := D.perturbedBottom
  perturbedSecond := D.perturbedSecond
  radius := D.primeFamily.radius
  bottom_upper := D.bottom_upper
  second_lower := D.second_lower

/-- The base gap of the associated two-level datum. -/
def baseGap
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ)
    (a : Scale) : ℝ :=
  scaleBaseGap (D.toScaleTwoLevelDeviation) a

/-- The perturbed gap of the associated two-level datum. -/
def perturbedGap
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ)
    (a : Scale) : ℝ :=
  scalePerturbedGap (D.toScaleTwoLevelDeviation) a

/-- CCM Kato/Weyl data supplies the scale-indexed gap lower bound. -/
theorem gap_lower_bound
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ)
    (a : Scale) :
    D.baseGap a - 2 * D.primeFamily.radius a ≤ D.perturbedGap a :=
  scale_gap_lower_bound (D.toScaleTwoLevelDeviation) a

/-- Small finite CCM radius keeps the associated perturbed gap positive. -/
theorem positiveGap_of_katoSmall
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ)
    (hsmall : ∀ a : Scale,
      2 * D.primeFamily.radius a < D.baseGap a) :
    CVSGapPreservation.PositiveGap D.perturbedGap :=
  positiveGap_of_scaleTwoLevelDeviation D.toScaleTwoLevelDeviation hsmall

end CCMKatoWeylData

/--
Packaged C-vS certificate with a finite CCM Frobenius radius source.

The certificate is intentionally conditional: the finite Frobenius row gives a
candidate perturbation radius, while the eigenvalue-deviation, gap calibration,
and convergence rows remain explicit.
-/
structure CCMKatoWeylRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  gapData : CVSGapPreservation.GroundStateGapData groundStateData
  ccmData : CCMKatoWeylData approximants.Scale ι κ
  gap_eq :
    ∀ a : approximants.Scale,
      gapData.gap a = ccmData.perturbedGap a
  katoSmall :
    ∀ a : approximants.Scale,
      2 * ccmData.primeFamily.radius a < ccmData.baseGap a
  convergesToXi : convergence.convergesToXi

namespace CCMKatoWeylRHCertificate

/-- A packaged finite-CCM Kato/Weyl C-vS certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : CCMKatoWeylRHCertificate.{u} (ι := ι) (κ := κ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_scaleTwoLevelDeviation_and_convergence
    cert.groundStateData cert.convergence cert.gapData
    cert.ccmData.toScaleTwoLevelDeviation cert.gap_eq
    cert.katoSmall cert.convergesToXi

end CCMKatoWeylRHCertificate

end CCMFiniteKatoBridge
end JensenLadder
