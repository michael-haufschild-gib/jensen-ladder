import JensenLadder.SpectralRealization

/-!
# Moment-problem carrier boundary

This file records the Hamburger/moment-problem face of the current RH frontier.

The point is deliberately narrow.  We do not formalize the Hamburger moment
theorem, build a positive Hankel form for `Xi`, construct a representing
measure, or prove RH.  Instead, we isolate the rows a moment-problem proof would
need before it can hand off to the already-formalized regular `Xi` spectral
endpoint:

* a Hankel-positivity row;
* a representing-measure row;
* a dictionary row saying that the real support of that measure is exactly the
  regular `Xi` zero set.

This is the Lean-facing form of the invariant: spectral/moment realizability is
useful only at exact per-zero faithfulness.  Density, positivity language, or a
real support object without the exact zero dictionary does not prove RH.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace MomentProblemCarrier

open SpectralRealization

universe u

/--
An abstract moment-problem carrier for the regular `Xi` zeros.

`moments` is included to mark the intended Hankel data.  The fields
`hankelPositive` and `representingMeasure` are propositions because this module
does not construct or analyze the moment problem.  The load-bearing adapter is
`zeroDictionary_of_momentRows`: it must turn those moment rows into exact
soundness and completeness for the regular `Xi` zero set.
-/
structure Carrier where
  Support : Type u
  height : Support -> ℝ
  moments : ℕ -> ℝ
  hankelPositive : Prop
  representingMeasure : Prop
  zeroDictionary : Prop
  zeroDictionary_of_momentRows :
    hankelPositive -> representingMeasure -> zeroDictionary
  sound_of_dictionary : zeroDictionary -> RegularXiZeroSoundness height
  complete_of_dictionary : zeroDictionary -> RegularXiZeroCompleteness height

/-- The moment rows required before the carrier can be used as an RH handoff. -/
def Carrier.FaithfulRows (C : Carrier.{u}) : Prop :=
  C.hankelPositive ∧ C.representingMeasure

/-- The exact zero dictionary supplied by faithful moment rows. -/
def Carrier.zeroDictionary_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.zeroDictionary :=
  C.zeroDictionary_of_momentRows h.1 h.2

/-- Faithful moment rows supply an exact regular spectral realization. -/
def regularSpectralRealization_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := C.Support
  height := C.height
  sound := C.sound_of_dictionary (C.zeroDictionary_of_faithfulRows h)
  complete := C.complete_of_dictionary (C.zeroDictionary_of_faithfulRows h)

/--
A non-circular moment-problem carrier with exact faithful rows would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_faithfulRows C h)

/-- A regular `Xi` zero not represented by the carrier's real support. -/
def MissingRegularXiZero (C : Carrier.{u}) : Prop :=
  exists z : ℂ, RHReduction.riemannXiRegularZero z ∧
    forall γ : C.Support, z ≠ (C.height γ : ℂ)

/-- The zero dictionary rules out unrepresented regular `Xi` zeros. -/
theorem no_missingRegularXiZero_of_zeroDictionary
    (C : Carrier.{u})
    (hdict : C.zeroDictionary) :
    ¬ MissingRegularXiZero C := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases C.complete_of_dictionary hdict z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missing regular zero blocks the zero dictionary. -/
theorem not_zeroDictionary_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : MissingRegularXiZero C) :
    ¬ C.zeroDictionary := by
  intro hdict
  exact no_missingRegularXiZero_of_zeroDictionary C hdict hmiss

/-- A missing regular zero blocks the moment-problem faithful rows. -/
theorem not_faithfulRows_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : MissingRegularXiZero C) :
    ¬ C.FaithfulRows := by
  intro hrows
  exact not_zeroDictionary_of_missingRegularXiZero C hmiss
    (C.zeroDictionary_of_faithfulRows hrows)

/-- A non-real regular `Xi` zero is missing from every real-support carrier. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    MissingRegularXiZero C := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (by
    rw [hγ]
    simp)

/-- A non-real regular `Xi` zero blocks the moment-problem faithful rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows :=
  not_faithfulRows_of_missingRegularXiZero C
    (missingRegularXiZero_of_nonrealRegularXiZero C hz hzim)

/-- Existence of a faithful moment-problem carrier. -/
def HasFaithfulMomentProblemCarrier : Prop :=
  exists C : Carrier.{u}, C.FaithfulRows

/-- A faithful moment-problem carrier supplies an exact regular spectral realization. -/
theorem nonempty_regularSpectralRealization_of_hasFaithfulMomentProblemCarrier
    (hC : HasFaithfulMomentProblemCarrier.{u}) :
    Nonempty RiemannXiRegularSpectralRealization.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨regularSpectralRealization_of_faithfulRows C hrows⟩

/--
Circular calibration: an already exact regular spectral realization can be
viewed as a moment-problem carrier with trivial moment rows.

This is not a construction of a Hamburger measure from `Xi`; it simply shows
that the interface has no hidden strength beyond exact real-support
faithfulness.
-/
def momentCarrierOfRegularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    Carrier.{u} where
  Support := S.Spectrum
  height := S.height
  moments := fun _ => 0
  hankelPositive := True
  representingMeasure := True
  zeroDictionary := True
  zeroDictionary_of_momentRows := by
    intro _hpos _hmeas
    trivial
  sound_of_dictionary := by
    intro _hdict
    exact S.sound
  complete_of_dictionary := by
    intro _hdict
    exact S.complete

/-- The calibrated carrier is faithful. -/
theorem faithfulRows_momentCarrierOfRegularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    (momentCarrierOfRegularSpectralRealization S).FaithfulRows :=
  ⟨trivial, trivial⟩

/-- An exact regular spectral realization supplies the calibrated moment carrier. -/
theorem hasFaithfulMomentProblemCarrier_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    HasFaithfulMomentProblemCarrier.{u} :=
  ⟨momentCarrierOfRegularSpectralRealization S,
    faithfulRows_momentCarrierOfRegularSpectralRealization S⟩

/-- A nonempty exact spectral realization supplies the calibrated moment carrier. -/
theorem hasFaithfulMomentProblemCarrier_of_nonempty_regularSpectralRealization
    (hS : Nonempty RiemannXiRegularSpectralRealization.{u}) :
    HasFaithfulMomentProblemCarrier.{u} := by
  rcases hS with ⟨S⟩
  exact hasFaithfulMomentProblemCarrier_of_regularSpectralRealization S

/--
The moment-problem carrier handoff is exactly the existing regular spectral
endpoint.

The reverse direction is the circular calibration above; it does not construct
the Hankel positivity or representing measure non-circularly.
-/
theorem hasFaithfulMomentProblemCarrier_iff_regularSpectralRealization :
    HasFaithfulMomentProblemCarrier.{u} ↔
      Nonempty RiemannXiRegularSpectralRealization.{u} := by
  constructor
  · exact nonempty_regularSpectralRealization_of_hasFaithfulMomentProblemCarrier
  · exact hasFaithfulMomentProblemCarrier_of_nonempty_regularSpectralRealization

/--
At universe zero, the moment-problem handoff has exactly RH strength.

The forward direction is the conditional Hamburger/moment-problem route.  The
reverse direction is only the tautological spectral support calibration.
-/
theorem hasFaithfulMomentProblemCarrier_iff_riemannHypothesis :
    HasFaithfulMomentProblemCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulMomentProblemCarrier_iff_regularSpectralRealization.trans
    nonempty_regularSpectralRealization_iff_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful moment-problem carrier. -/
theorem not_hasFaithfulMomentProblemCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulMomentProblemCarrier.{u} := by
  rintro ⟨C, hrows⟩
  exact not_faithfulRows_of_nonrealRegularXiZero C hz hzim hrows

/-- Packaged conditional certificate for the moment-problem route. -/
structure MomentProblemRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace MomentProblemRHCertificate

/-- The packaged moment-problem certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : MomentProblemRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_faithfulRows C.carrier C.faithfulRows

/-- The packaged certificate supplies an exact regular spectral realization. -/
def regularSpectralRealization
    (C : MomentProblemRHCertificate.{u}) :
    RiemannXiRegularSpectralRealization.{u} :=
  regularSpectralRealization_of_faithfulRows C.carrier C.faithfulRows

end MomentProblemRHCertificate

end MomentProblemCarrier
end JensenLadder
