import JensenLadder.CCMFiniteKatoBridge
import Mathlib.Tactic

/-!
# Kato-smallness no-go under critical gap collapse

This module records the finite ordered-field obstruction behind the C-vS/CCM
gap-preservation route:

```text
gap(a) becomes arbitrarily small,   radius(a) >= r0 > 0
----------------------------------------------------------
not (∀ a, 2 * radius(a) < gap(a)).
```

So a Kato-small proof cannot be uniform when the unperturbed bottom gap closes
while the semilocal prime perturbation radius has a positive floor.  This is a
dead-end elimination row, not a proof or disproof of RH.

Evidence class: dead-end elimination / formal-certificate artifact.  Theorem M
is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace CVSKatoSmallNoGo

open CVSGapPreservation
open CVSKatoWeyl
open CCMFiniteKatoBridge

universe u

/-- A scale-indexed gap has no positive lower floor: it drops below every
positive threshold somewhere in the scale family. -/
def GapArbitrarilySmall {Scale : Type u} (gap : Scale → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : Scale, gap a < ε

/-- A scale-indexed perturbation radius has a positive lower floor. -/
def RadiusHasPositiveFloor {Scale : Type u} (radius : Scale → ℝ) : Prop :=
  ∃ r0 : ℝ, 0 < r0 ∧ ∀ a : Scale, r0 ≤ radius a

/-- The Kato-small row is impossible if the unperturbed gap becomes
arbitrarily small while the perturbation radius has a positive floor. -/
theorem not_katoSmall_of_gapArbitrarilySmall_and_radiusFloor
    {Scale : Type u}
    (B : GapBudget Scale)
    (hgap : GapArbitrarilySmall B.unperturbedGap)
    (hradius : RadiusHasPositiveFloor B.perturbationRadius) :
    ¬ KatoSmall B := by
  intro hsmall
  rcases hradius with ⟨r0, hr0, hfloor⟩
  rcases hgap (2 * r0) (by linarith) with ⟨a, hgap_lt⟩
  have hradius_floor : 2 * r0 ≤ 2 * B.perturbationRadius a := by
    linarith [hfloor a]
  linarith [hsmall a, hgap_lt, hradius_floor]

/-- Two-level Kato-smallness is impossible under the same gap-collapse and
positive-radius-floor hypotheses. -/
theorem not_scaleTwoLevel_katoSmall_of_gapArbitrarilySmall_and_radiusFloor
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (hgap : GapArbitrarilySmall (scaleBaseGap D))
    (hradius : RadiusHasPositiveFloor D.radius) :
    ¬ (∀ a : Scale, 2 * D.radius a < scaleBaseGap D a) := by
  intro hsmall
  exact not_katoSmall_of_gapArbitrarilySmall_and_radiusFloor
    (gapBudgetOfScaleTwoLevelDeviation D) hgap hradius hsmall

/-- The `GapBudget` built from two-level deviation data is not Kato-small under
critical gap collapse with a positive perturbation-radius floor. -/
theorem not_gapBudgetOfScaleTwoLevelDeviation_katoSmall
    {Scale : Type u}
    (D : ScaleTwoLevelDeviation Scale)
    (hgap : GapArbitrarilySmall (scaleBaseGap D))
    (hradius : RadiusHasPositiveFloor D.radius) :
    ¬ KatoSmall (gapBudgetOfScaleTwoLevelDeviation D) :=
  not_katoSmall_of_gapArbitrarilySmall_and_radiusFloor
    (gapBudgetOfScaleTwoLevelDeviation D) hgap hradius

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Finite CCM Kato/Weyl data cannot satisfy the small-radius row when its base
gap collapses and its finite CCM perturbation radius has a positive floor. -/
theorem not_ccmKatoSmall_of_gapArbitrarilySmall_and_radiusFloor
    {Scale : Type u}
    (D : CCMKatoWeylData Scale ι κ)
    (hgap : GapArbitrarilySmall D.baseGap)
    (hradius : RadiusHasPositiveFloor D.primeFamily.radius) :
    ¬ (∀ a : Scale, 2 * D.primeFamily.radius a < D.baseGap a) := by
  exact not_scaleTwoLevel_katoSmall_of_gapArbitrarilySmall_and_radiusFloor
    D.toScaleTwoLevelDeviation hgap hradius

/-- A packaged finite-CCM Kato/Weyl certificate is inconsistent with a
collapsing base gap and positive prime-radius floor for its own CCM data. -/
theorem false_of_ccmKatoWeylCertificate_gapArbitrarilySmall_and_radiusFloor
    (cert : CCMKatoWeylRHCertificate.{u} (ι := ι) (κ := κ))
    (hgap : GapArbitrarilySmall cert.ccmData.baseGap)
    (hradius : RadiusHasPositiveFloor cert.ccmData.primeFamily.radius) :
    False := by
  exact not_ccmKatoSmall_of_gapArbitrarilySmall_and_radiusFloor
    cert.ccmData hgap hradius cert.katoSmall

end CVSKatoSmallNoGo
end JensenLadder
