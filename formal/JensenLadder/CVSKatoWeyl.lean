import JensenLadder.CVSGapPreservation
import Mathlib.Tactic

/-!
# Two-level Weyl/Kato gap algebra for the C-vS route

This module isolates the elementary algebra behind the usual finite
gap-preservation estimate:

```text
perturbed_bottom <= base_bottom + r,
base_second - r <= perturbed_second
------------------------------------------------
perturbed_gap >= base_gap - 2r.
```

The analytic work is proving the two eigenvalue-deviation rows for a concrete
semilocal CCM/Sonin operator.  Once those rows are available, this module
builds the `CVSGapPreservation.GapBudget` shape consumed by the C-vS route.

It does not prove eigenvalue perturbation theory, min-max principles,
ground-state simplicity, convergence, positivity, or the Riemann Hypothesis.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CVSKatoWeyl

open CVSSpectralRoute
open CVSGapPreservation

universe u

/-- One finite two-level perturbation datum.  The rows mean: the perturbed
bottom level is no higher than `baseBottom + radius`, and the perturbed second
level is no lower than `baseSecond - radius`. -/
structure TwoLevelDeviation where
  baseBottom : ℝ
  baseSecond : ℝ
  perturbedBottom : ℝ
  perturbedSecond : ℝ
  radius : ℝ
  bottom_upper : perturbedBottom ≤ baseBottom + radius
  second_lower : baseSecond - radius ≤ perturbedSecond

/-- Unperturbed bottom-to-second gap for a two-level datum. -/
def twoLevelBaseGap (D : TwoLevelDeviation) : ℝ :=
  D.baseSecond - D.baseBottom

/-- Perturbed bottom-to-second gap for a two-level datum. -/
def twoLevelPerturbedGap (D : TwoLevelDeviation) : ℝ :=
  D.perturbedSecond - D.perturbedBottom

/-- The two eigenvalue-deviation rows imply the standard gap lower bound. -/
theorem twoLevel_gap_lower_bound
    (D : TwoLevelDeviation) :
    twoLevelBaseGap D - 2 * D.radius ≤ twoLevelPerturbedGap D := by
  unfold twoLevelBaseGap twoLevelPerturbedGap
  linarith [D.bottom_upper, D.second_lower]

/-- Scale-indexed two-level perturbation data. -/
structure ScaleTwoLevelDeviation (Scale : Type u) where
  baseBottom : Scale → ℝ
  baseSecond : Scale → ℝ
  perturbedBottom : Scale → ℝ
  perturbedSecond : Scale → ℝ
  radius : Scale → ℝ
  bottom_upper :
    ∀ a : Scale, perturbedBottom a ≤ baseBottom a + radius a
  second_lower :
    ∀ a : Scale, baseSecond a - radius a ≤ perturbedSecond a

/-- Scale-indexed unperturbed bottom-to-second gap. -/
def scaleBaseGap {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (a : Scale) : ℝ :=
  D.baseSecond a - D.baseBottom a

/-- Scale-indexed perturbed bottom-to-second gap. -/
def scalePerturbedGap {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (a : Scale) : ℝ :=
  D.perturbedSecond a - D.perturbedBottom a

/-- Pointwise gap lower bound from scale-indexed two-level deviation rows. -/
theorem scale_gap_lower_bound
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (a : Scale) :
    scaleBaseGap D a - 2 * D.radius a ≤ scalePerturbedGap D a := by
  unfold scaleBaseGap scalePerturbedGap
  linarith [D.bottom_upper a, D.second_lower a]

/-- The two-level deviation rows produce the exact `GapBudget` consumed by the
C-vS gap-preservation handoff. -/
def gapBudgetOfScaleTwoLevelDeviation
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale) :
    GapBudget Scale where
  unperturbedGap := scaleBaseGap D
  perturbationRadius := D.radius
  perturbedGap := scalePerturbedGap D
  gap_lower_bound := scale_gap_lower_bound D

/-- The usual `2r < base_gap` row is definitionally the `KatoSmall` condition
for the gap budget built from two-level deviation data. -/
theorem katoSmall_gapBudgetOfScaleTwoLevelDeviation_iff
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale) :
    KatoSmall (gapBudgetOfScaleTwoLevelDeviation D) ↔
      ∀ a : Scale, 2 * D.radius a < scaleBaseGap D a := by
  rfl

/-- A small two-level perturbation keeps the perturbed gap positive at every
scale. -/
theorem positiveGap_of_scaleTwoLevelDeviation
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (hsmall : ∀ a : Scale, 2 * D.radius a < scaleBaseGap D a) :
    PositiveGap (scalePerturbedGap D) := by
  intro a
  have hdiff : 0 < scaleBaseGap D a - 2 * D.radius a := by
    linarith [hsmall a]
  linarith [scale_gap_lower_bound D a]

/-- A calibrated two-level gap estimate supplies finite simple-even ground
states. -/
theorem simpleEvenGroundStates_of_scaleTwoLevelDeviation
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (gapData : GroundStateGapData G)
    (D : ScaleTwoLevelDeviation A.Scale)
    (hgap : ∀ a : A.Scale,
      gapData.gap a = scalePerturbedGap D a)
    (hsmall : ∀ a : A.Scale,
      2 * D.radius a < scaleBaseGap D a) :
    SimpleEvenGroundStates G := by
  apply simpleEvenGroundStates_of_positiveGap gapData
  intro a
  rw [hgap a]
  exact positiveGap_of_scaleTwoLevelDeviation D hsmall a

/-- Two-level Weyl/Kato rows plus the C-vS convergence row prove RH through the
existing spectral route. -/
theorem riemannHypothesis_of_scaleTwoLevelDeviation_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (gapData : GroundStateGapData G)
    (D : ScaleTwoLevelDeviation A.Scale)
    (hgap : ∀ a : A.Scale,
      gapData.gap a = scalePerturbedGap D a)
    (hsmall : ∀ a : A.Scale,
      2 * D.radius a < scaleBaseGap D a)
    (hconv : H.convergesToXi) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence G H
    (simpleEvenGroundStates_of_scaleTwoLevelDeviation
      gapData D hgap hsmall)
    hconv

/--
Packaged C-vS certificate using two-level Weyl/Kato gap rows.

The load-bearing analytic fields remain explicit: a concrete operator family
must supply the two eigenvalue-deviation inequalities, the smallness row, the
calibration from positive gap to simple-even ground state, and convergence to
`Xi`.
-/
structure KatoWeylRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  gapData : GroundStateGapData groundStateData
  twoLevelData : ScaleTwoLevelDeviation approximants.Scale
  gap_eq :
    ∀ a : approximants.Scale,
      gapData.gap a = scalePerturbedGap twoLevelData a
  katoSmall :
    ∀ a : approximants.Scale,
      2 * twoLevelData.radius a < scaleBaseGap twoLevelData a
  convergesToXi : convergence.convergesToXi

namespace KatoWeylRHCertificate

/-- A packaged two-level Weyl/Kato C-vS certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : KatoWeylRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_scaleTwoLevelDeviation_and_convergence
    cert.groundStateData cert.convergence cert.gapData
    cert.twoLevelData cert.gap_eq cert.katoSmall cert.convergesToXi

end KatoWeylRHCertificate

end CVSKatoWeyl
end JensenLadder
