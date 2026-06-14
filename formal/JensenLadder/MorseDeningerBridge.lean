import JensenLadder.DeningerCarrier
import JensenLadder.MorseCriterion

/-!
# Morse-to-Deninger endpoint bridge

This file connects two already-separated spectral-route interfaces:

* `MorseCriterion.MorseIndexSpectralCriterion`, where zero negative index at
  every scale supplies an exact regular `Xi` spectral realization;
* `DeningerCarrier.HasPolarizedFaithfulDictionary`, the calibrated
  Deninger-style carrier handoff.

The bridge is only composition.  It does not construct a zeta/CCM/Suzuki Morse
criterion, Deninger's cohomology, a positivity theorem, or RH.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace MorseDeningerBridge

open DeningerCarrier
open MorseCriterion

universe u

/--
Zero negative modes for a supplied spectral Morse criterion provide the
calibrated Deninger-style faithful carrier.
-/
theorem hasPolarizedFaithfulDictionary_of_noNegativeModes
    (C : MorseIndexSpectralCriterion.{u})
    (hzero : NoNegativeModes C.negativeIndex) :
    HasPolarizedFaithfulDictionary.{0} :=
  hasPolarizedFaithfulDictionary_of_regularSpectralRealization
    (C.realization_of_noNegativeModes hzero)

/--
For a supplied spectral Morse criterion, zero negative modes are equivalent to
the faithful Deninger-style carrier handoff.

This is not a new proof route: the right-to-left direction passes from the
faithful carrier back through the exact regular spectral realization.
-/
theorem noNegativeModes_iff_hasPolarizedFaithfulDictionary
    (C : MorseIndexSpectralCriterion.{u}) :
    NoNegativeModes C.negativeIndex ↔ HasPolarizedFaithfulDictionary.{0} := by
  constructor
  · exact hasPolarizedFaithfulDictionary_of_noNegativeModes C
  · intro hcarrier
    rcases nonempty_regularSpectralRealization_of_hasPolarizedFaithfulDictionary hcarrier with ⟨S⟩
    exact C.noNegativeModes_of_realization S

/--
For a supplied spectral Morse criterion, mathlib's `RiemannHypothesis`, zero
negative modes, and the faithful carrier handoff are the same endpoint.
-/
theorem riemannHypothesis_iff_hasPolarizedFaithfulDictionary
    (_C : MorseIndexSpectralCriterion.{u}) :
    RiemannHypothesis ↔ HasPolarizedFaithfulDictionary.{0} :=
  hasPolarizedFaithfulDictionary_iff_riemannHypothesis.symm

/--
A certified negative mode rules out the faithful Deninger-style carrier handoff
under the supplied spectral Morse criterion.
-/
theorem not_hasPolarizedFaithfulDictionary_of_negativeIndex_ne_zero
    (C : MorseIndexSpectralCriterion.{u}) {a : C.Scale}
    (ha : C.negativeIndex a ≠ 0) :
    ¬ HasPolarizedFaithfulDictionary.{0} := by
  intro hcarrier
  have hzero : NoNegativeModes C.negativeIndex :=
    (noNegativeModes_iff_hasPolarizedFaithfulDictionary C).2 hcarrier
  exact ha (hzero a)

/-- Packaged Morse-to-Deninger RH certificate. -/
structure MorseDeningerRHCertificate where
  criterion : MorseIndexSpectralCriterion.{u}
  noNegativeModes : NoNegativeModes criterion.negativeIndex

namespace MorseDeningerRHCertificate

/-- The packaged certificate supplies the faithful Deninger-style carrier. -/
theorem hasPolarizedFaithfulDictionary
    (cert : MorseDeningerRHCertificate.{u}) :
    HasPolarizedFaithfulDictionary.{0} :=
  hasPolarizedFaithfulDictionary_of_noNegativeModes cert.criterion cert.noNegativeModes

/-- The packaged certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : MorseDeningerRHCertificate.{u}) :
    RiemannHypothesis :=
  (hasPolarizedFaithfulDictionary_iff_riemannHypothesis).1
    (hasPolarizedFaithfulDictionary cert)

end MorseDeningerRHCertificate

/-- Packaged negative-mode obstruction to the faithful carrier handoff. -/
structure MorseDeningerFalsifier where
  criterion : MorseIndexSpectralCriterion.{u}
  scale : criterion.Scale
  negativeIndex_ne_zero : criterion.negativeIndex scale ≠ 0

namespace MorseDeningerFalsifier

/-- A packaged negative mode blocks the faithful Deninger-style carrier. -/
theorem not_hasPolarizedFaithfulDictionary
    (cert : MorseDeningerFalsifier.{u}) :
    ¬ HasPolarizedFaithfulDictionary.{0} :=
  not_hasPolarizedFaithfulDictionary_of_negativeIndex_ne_zero
    cert.criterion cert.negativeIndex_ne_zero

/-- A packaged negative mode refutes mathlib's `RiemannHypothesis`. -/
theorem not_riemannHypothesis
    (cert : MorseDeningerFalsifier.{u}) :
    ¬ RiemannHypothesis :=
  MorseCriterion.not_riemannHypothesis_of_negativeIndex_ne_zero
    cert.criterion cert.negativeIndex_ne_zero

end MorseDeningerFalsifier

end MorseDeningerBridge
end JensenLadder
