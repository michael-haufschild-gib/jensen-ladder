import JensenLadder.SpectralRealization

/-!
# Deninger carrier boundary

This file records the Lean-facing consequence of a Deninger-style polarized
arithmetic cohomology carrier.

The mathematical content is intentionally narrow.  A polarization or
Hodge-index package is not represented here as analytic functional analysis;
instead, it is represented by the exact zero dictionary it must ultimately
deliver to the already-formalized `SpectralRealization` endpoint.  Thus the
load-bearing row is `zeroDictionary`: it must supply both soundness and
completeness for the regular `Xi` zero set by real spectral heights.

This module does not construct Deninger's `H*_dyn`, a flow, a determinant
identity, a positivity theorem, or the Riemann Hypothesis.  It only names the
conditional carrier interface and its missing-zero falsifier.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace DeningerCarrier

open SpectralRealization

universe u

/--
A Deninger/Hodge-index-shaped spectral carrier for the regular `Xi` zeros.

`carrierPolarized` records the external geometric/cohomological positivity
package.  The Lean proof of RH below does not get RH from the name
"polarized"; it gets RH from `zeroDictionary`, via the supplied soundness and
completeness rows.  That is the intended boundary: polarization must deliver an
exact non-circular zero dictionary.
-/
structure PolarizedSpectralCarrier where
  Spectrum : Type u
  height : Spectrum -> ℝ
  carrierPolarized : Prop
  zeroDictionary : Prop
  sound_of_dictionary : zeroDictionary -> RegularXiZeroSoundness height
  complete_of_dictionary : zeroDictionary -> RegularXiZeroCompleteness height

/--
The combined Deninger-style handoff: a polarized carrier plus its exact zero
dictionary.

The polarization component is bookkeeping for the external Hodge-index theorem;
the dictionary component is the formal row that interfaces with
`SpectralRealization`.
-/
def PolarizedFaithfulDictionary (D : PolarizedSpectralCarrier.{u}) : Prop :=
  D.carrierPolarized ∧ D.zeroDictionary

/-- A regular `Xi` zero not represented by the carrier's real spectral heights. -/
def MissingRegularXiZero (D : PolarizedSpectralCarrier.{u}) : Prop :=
  exists z : ℂ, RHReduction.riemannXiRegularZero z ∧
    forall γ : D.Spectrum, z ≠ (D.height γ : ℂ)

/--
A polarized faithful dictionary supplies the existing exact regular spectral
realization endpoint.
-/
def regularSpectralRealization_of_polarizedFaithfulDictionary
    (D : PolarizedSpectralCarrier.{u})
    (h : PolarizedFaithfulDictionary D) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := D.Spectrum
  height := D.height
  sound := D.sound_of_dictionary h.2
  complete := D.complete_of_dictionary h.2

/--
A non-circular construction of a polarized carrier with an exact zero
dictionary would prove mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_polarizedFaithfulDictionary
    (D : PolarizedSpectralCarrier.{u})
    (h : PolarizedFaithfulDictionary D) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_polarizedFaithfulDictionary D h)

/-- The zero dictionary rules out unrepresented regular `Xi` zeros. -/
theorem no_missingRegularXiZero_of_zeroDictionary
    (D : PolarizedSpectralCarrier.{u})
    (hdict : D.zeroDictionary) :
    ¬ MissingRegularXiZero D := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases D.complete_of_dictionary hdict z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missing regular zero falsifies the zero dictionary. -/
theorem not_zeroDictionary_of_missingRegularXiZero
    (D : PolarizedSpectralCarrier.{u})
    (hmiss : MissingRegularXiZero D) :
    ¬ D.zeroDictionary := by
  intro hdict
  exact no_missingRegularXiZero_of_zeroDictionary D hdict hmiss

/-- A missing regular zero blocks the polarized faithful handoff. -/
theorem not_polarizedFaithfulDictionary_of_missingRegularXiZero
    (D : PolarizedSpectralCarrier.{u})
    (hmiss : MissingRegularXiZero D) :
    ¬ PolarizedFaithfulDictionary D := by
  intro hfaithful
  exact not_zeroDictionary_of_missingRegularXiZero D hmiss hfaithful.2

/-- A non-real regular `Xi` zero is missing from every real-height carrier. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (D : PolarizedSpectralCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    MissingRegularXiZero D := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (by
    rw [hγ]
    simp)

/-- A non-real regular `Xi` zero falsifies any real-height zero dictionary. -/
theorem not_zeroDictionary_of_nonrealRegularXiZero
    (D : PolarizedSpectralCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ D.zeroDictionary :=
  not_zeroDictionary_of_missingRegularXiZero D
    (missingRegularXiZero_of_nonrealRegularXiZero D hz hzim)

/-- A non-real regular `Xi` zero blocks the polarized faithful carrier handoff. -/
theorem not_polarizedFaithfulDictionary_of_nonrealRegularXiZero
    (D : PolarizedSpectralCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ PolarizedFaithfulDictionary D :=
  not_polarizedFaithfulDictionary_of_missingRegularXiZero D
    (missingRegularXiZero_of_nonrealRegularXiZero D hz hzim)

/-- A non-real regular `Xi` zero directly falsifies mathlib's RH. -/
theorem not_riemannHypothesis_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact hzim
    ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1 hRH z hz)

/-- Existence of a polarized faithful dictionary at a fixed universe level. -/
def HasPolarizedFaithfulDictionary : Prop :=
  exists D : PolarizedSpectralCarrier.{u}, PolarizedFaithfulDictionary D

/-- A non-real regular `Xi` zero rules out every faithful Deninger carrier handoff. -/
theorem not_hasPolarizedFaithfulDictionary_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasPolarizedFaithfulDictionary.{u} := by
  rintro ⟨D, hfaithful⟩
  exact not_polarizedFaithfulDictionary_of_nonrealRegularXiZero D hz hzim hfaithful

/--
The tautological polarized carrier obtained from an already exact regular
spectral realization.

This is deliberately circular as a proof method: it takes the exact spectral
realization as input and labels its carrier as polarized with `True`.  It is
only a calibration showing that the Deninger-carrier interface has no hidden
extra strength beyond exact spectral identification.
-/
def polarizedCarrierOfRegularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    PolarizedSpectralCarrier.{u} where
  Spectrum := S.Spectrum
  height := S.height
  carrierPolarized := True
  zeroDictionary := True
  sound_of_dictionary := by
    intro _h
    exact S.sound
  complete_of_dictionary := by
    intro _h
    exact S.complete

/-- An exact regular spectral realization supplies the calibrated faithful dictionary. -/
theorem polarizedFaithfulDictionary_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    PolarizedFaithfulDictionary (polarizedCarrierOfRegularSpectralRealization S) :=
  ⟨trivial, trivial⟩

/-- An exact regular spectral realization gives a nonempty faithful carrier handoff. -/
theorem hasPolarizedFaithfulDictionary_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    HasPolarizedFaithfulDictionary.{u} :=
  ⟨polarizedCarrierOfRegularSpectralRealization S,
    polarizedFaithfulDictionary_of_regularSpectralRealization S⟩

/-- A nonempty exact spectral realization gives a nonempty faithful carrier handoff. -/
theorem hasPolarizedFaithfulDictionary_of_nonempty_regularSpectralRealization
    (hS : Nonempty RiemannXiRegularSpectralRealization.{u}) :
    HasPolarizedFaithfulDictionary.{u} := by
  rcases hS with ⟨S⟩
  exact hasPolarizedFaithfulDictionary_of_regularSpectralRealization S

/-- A faithful carrier handoff gives a nonempty exact regular spectral realization. -/
theorem nonempty_regularSpectralRealization_of_hasPolarizedFaithfulDictionary
    (hD : HasPolarizedFaithfulDictionary.{u}) :
    Nonempty RiemannXiRegularSpectralRealization.{u} := by
  rcases hD with ⟨D, hfaithful⟩
  exact ⟨regularSpectralRealization_of_polarizedFaithfulDictionary D hfaithful⟩

/--
The Deninger-carrier handoff is exactly the existing regular spectral endpoint.

The reverse direction is the tautological calibration above, so it is not a
construction of Deninger's cohomology or positivity.
-/
theorem hasPolarizedFaithfulDictionary_iff_regularSpectralRealization :
    HasPolarizedFaithfulDictionary.{u} ↔
      Nonempty RiemannXiRegularSpectralRealization.{u} := by
  constructor
  · exact nonempty_regularSpectralRealization_of_hasPolarizedFaithfulDictionary
  · exact hasPolarizedFaithfulDictionary_of_nonempty_regularSpectralRealization

/--
At universe zero, the faithful Deninger-carrier handoff has exactly RH strength.

The forward direction is the conditional Deninger/Hodge-index route.  The reverse
direction is the tautological zero-set/spectral carrier calibration inherited
from `SpectralRealization`.
-/
theorem hasPolarizedFaithfulDictionary_iff_riemannHypothesis :
    HasPolarizedFaithfulDictionary.{0} ↔ RiemannHypothesis := by
  exact hasPolarizedFaithfulDictionary_iff_regularSpectralRealization.trans
    nonempty_regularSpectralRealization_iff_riemannHypothesis

/-- Packaged conditional RH certificate for the Deninger carrier route. -/
structure PolarizedSpectralRHCertificate where
  carrier : PolarizedSpectralCarrier.{u}
  faithfulDictionary : PolarizedFaithfulDictionary carrier

/-- The packaged Deninger-carrier certificate proves mathlib's RH. -/
theorem riemannHypothesis_of_certificate
    (C : PolarizedSpectralRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_polarizedFaithfulDictionary C.carrier C.faithfulDictionary

end DeningerCarrier
end JensenLadder
