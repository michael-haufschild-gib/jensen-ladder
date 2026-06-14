import JensenLadder.CVSSpectralRoute
import Mathlib.Tactic

/-!
# Gap-preservation handoff for the C-vS route

This module isolates the finite spectral-gap estimate that the semilocal
operator route still needs.

The analytic target has the shape

```text
perturbed_gap(a) >= unperturbed_gap(a) - 2 * perturbation_radius(a),
2 * perturbation_radius(a) < unperturbed_gap(a).
```

Those two rows imply `0 < perturbed_gap(a)`, hence bottom-state simplicity
whenever a concrete min-max theorem has identified positive gap with simplicity.
The file does not prove the operator-norm bound, positivity improvement,
finite-to-limit convergence, or RH.  It only records the exact algebraic
handoff from a future perturbation estimate to the existing C-vS spectral route.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CVSGapPreservation

open CVSSpectralRoute

universe u

/-- A scale-indexed spectral gap is positive at every scale. -/
def PositiveGap {Scale : Type u} (gap : Scale → ℝ) : Prop :=
  ∀ a : Scale, 0 < gap a

/--
Kato-style gap budget for a prime/local perturbation of an archimedean base
operator.

`unperturbedGap` is the base bottom-to-second spectral gap, `perturbationRadius`
is the operator-size budget for the semilocal prime perturbation, and
`perturbedGap` is the resulting semilocal bottom gap.  The lower-bound field is
the abstract perturbation estimate; proving it for the CCM/Sonin operator is
analytic work outside this bookkeeping structure.
-/
structure GapBudget (Scale : Type u) where
  unperturbedGap : Scale → ℝ
  perturbationRadius : Scale → ℝ
  perturbedGap : Scale → ℝ
  gap_lower_bound :
    ∀ a : Scale,
      unperturbedGap a - 2 * perturbationRadius a ≤ perturbedGap a

/-- The small-perturbation condition that keeps the spectral gap open. -/
def KatoSmall {Scale : Type u} (B : GapBudget Scale) : Prop :=
  ∀ a : Scale, 2 * B.perturbationRadius a < B.unperturbedGap a

/-- The gap budget preserves a positive perturbed gap under the smallness row. -/
theorem positiveGap_of_katoSmall
    {Scale : Type u} (B : GapBudget Scale)
    (hsmall : KatoSmall B) :
    PositiveGap B.perturbedGap := by
  intro a
  have hdiff : 0 < B.unperturbedGap a - 2 * B.perturbationRadius a := by
    linarith [hsmall a]
  linarith [B.gap_lower_bound a]

/--
Calibration from a positive finite gap to the finite simple-even C-vS
hypothesis.

For concrete operators, `simpleBottom_of_gap_pos` is the min-max/nondegeneracy
row, while `evenGroundState_of_gap_pos` packages the FE/Perron--Frobenius
evenness row.  Neither is proved here.
-/
structure GroundStateGapData
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A) where
  gap : A.Scale → ℝ
  simpleBottom_of_gap_pos :
    ∀ a : A.Scale, 0 < gap a → G.simpleBottom a
  evenGroundState_of_gap_pos :
    ∀ a : A.Scale, 0 < gap a → G.evenGroundState a

/-- A positive calibrated gap supplies the finite simple-even C-vS hypothesis. -/
theorem simpleEvenGroundStates_of_positiveGap
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : GroundStateGapData G)
    (hgap : PositiveGap D.gap) :
    SimpleEvenGroundStates G := by
  intro a
  exact ⟨D.simpleBottom_of_gap_pos a (hgap a),
    D.evenGroundState_of_gap_pos a (hgap a)⟩

/-- A gap budget tied to the calibrated ground-state gap. -/
structure GapBudgetForGroundState
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A) where
  gapData : GroundStateGapData G
  budget : GapBudget A.Scale
  gap_eq_budget :
    ∀ a : A.Scale, gapData.gap a = budget.perturbedGap a

/-- A small perturbation budget supplies finite simple-even ground states. -/
theorem simpleEvenGroundStates_of_gapBudget
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : GapBudgetForGroundState G)
    (hsmall : KatoSmall D.budget) :
    SimpleEvenGroundStates G := by
  apply simpleEvenGroundStates_of_positiveGap D.gapData
  intro a
  rw [D.gap_eq_budget a]
  exact positiveGap_of_katoSmall D.budget hsmall a

/-- A successful gap-preservation estimate plus the convergence row proves RH
through the C-vS spectral route. -/
theorem riemannHypothesis_of_gapBudget_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (D : GapBudgetForGroundState G)
    (hsmall : KatoSmall D.budget)
    (hconv : H.convergesToXi) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence G H
    (simpleEvenGroundStates_of_gapBudget D hsmall) hconv

/-- Under the C-vS convergence row, a non-real regular `Xi` zero rules out the
gap-preservation smallness estimate. -/
theorem not_katoSmall_of_nonrealRegularXiZero_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (D : GapBudgetForGroundState G)
    (hconv : H.convergesToXi)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ KatoSmall D.budget := by
  intro hsmall
  exact not_convergence_of_nonrealRegularXiZero_and_simpleEvenGroundStates
    G H (simpleEvenGroundStates_of_gapBudget D hsmall) hz hzim hconv

/--
Packaged C-vS certificate using a gap-preservation budget.

The certificate is intentionally conditional: the fields `katoSmall` and
`convergesToXi` are the analytic rows that remain to be proved for a concrete
semilocal operator family.
-/
structure GapBudgetRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  gapBudgetData : GapBudgetForGroundState groundStateData
  katoSmall : KatoSmall gapBudgetData.budget
  convergesToXi : convergence.convergesToXi

namespace GapBudgetRHCertificate

/-- A packaged gap-budget C-vS certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : GapBudgetRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_gapBudget_and_convergence
    cert.groundStateData cert.convergence cert.gapBudgetData
    cert.katoSmall cert.convergesToXi

end GapBudgetRHCertificate

end CVSGapPreservation
end JensenLadder
