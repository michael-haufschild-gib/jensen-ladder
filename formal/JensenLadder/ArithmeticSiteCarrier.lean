import JensenLadder.DeningerCarrier

/-!
# Arithmetic-site carrier boundary

This file records the Lean-facing boundary for the surviving non-spectral
carrier route.

The current obstruction is not the absence of words like "Frobenius" or
"cohomology"; it is the absence of a zeta-attached arithmetic carrier whose
Frobenius/Lambda-ring structure, Hodge-index package, and Lefschetz trace
formula produce the exact zero dictionary consumed by `DeningerCarrier`.

This module therefore separates the proposed arithmetic rows from the spectral
dictionary row.  It does not construct the arithmetic site, prove a
Hodge-index theorem, prove a Lefschetz trace formula, or prove RH.  It only
formalizes the handoff and the circular calibration: wrapping an already exact
spectral carrier gives an arithmetic-site carrier with exactly the same
RH-strength, and no extra proof content.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace ArithmeticSiteCarrier

open DeningerCarrier

universe u

/--
An arithmetic-site/cohomological carrier candidate before it is collapsed into
a spectral dictionary.

The first three proposition fields are the genuinely non-spectral rows one
would expect from a Borger/Connes/Deninger-style construction:

* `frobeniusLifts`: commuting Frobenius/Lambda-ring/Adams operations;
* `hodgeIndexPackage`: intrinsic polarization or Hodge-index positivity;
* `lefschetzTraceFormula`: a trace formula tying the arithmetic dynamics to
  the `Xi` zero dictionary.

The final two adapter fields say how the Hodge and trace rows produce the
already-formalized `DeningerCarrier` handoff.  This is where a real proof would
have to supply non-circular mathematics.
-/
structure Carrier where
  Site : Type u
  frobeniusLifts : Prop
  hodgeIndexPackage : Prop
  lefschetzTraceFormula : Prop
  spectralCarrier : PolarizedSpectralCarrier.{u}
  carrierPolarized_of_hodgeIndex :
    hodgeIndexPackage -> spectralCarrier.carrierPolarized
  zeroDictionary_of_lefschetz :
    lefschetzTraceFormula -> spectralCarrier.zeroDictionary

/--
The three arithmetic rows required before the carrier can be handed to the
existing Deninger/spectral endpoint.
-/
def Carrier.FaithfulRows (C : Carrier.{u}) : Prop :=
  C.frobeniusLifts ∧ C.hodgeIndexPackage ∧ C.lefschetzTraceFormula

/-- The arithmetic rows supply the Deninger faithful dictionary handoff. -/
theorem polarizedFaithfulDictionary_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    PolarizedFaithfulDictionary C.spectralCarrier :=
  ⟨C.carrierPolarized_of_hodgeIndex h.2.1,
    C.zeroDictionary_of_lefschetz h.2.2⟩

/--
A non-circular arithmetic-site carrier with all three rows would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_polarizedFaithfulDictionary C.spectralCarrier
    (polarizedFaithfulDictionary_of_faithfulRows C h)

/-- A missing regular zero blocks the Lefschetz trace row. -/
theorem not_lefschetzTraceFormula_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : MissingRegularXiZero C.spectralCarrier) :
    ¬ C.lefschetzTraceFormula := by
  intro htrace
  exact not_zeroDictionary_of_missingRegularXiZero C.spectralCarrier hmiss
    (C.zeroDictionary_of_lefschetz htrace)

/-- A missing regular zero blocks the full arithmetic-site handoff. -/
theorem not_faithfulRows_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : MissingRegularXiZero C.spectralCarrier) :
    ¬ C.FaithfulRows := by
  intro hrows
  exact not_lefschetzTraceFormula_of_missingRegularXiZero C hmiss hrows.2.2

/-- A non-real regular `Xi` zero blocks the Lefschetz trace row. -/
theorem not_lefschetzTraceFormula_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.lefschetzTraceFormula :=
  not_lefschetzTraceFormula_of_missingRegularXiZero C
    (missingRegularXiZero_of_nonrealRegularXiZero C.spectralCarrier hz hzim)

/-- A non-real regular `Xi` zero blocks the full arithmetic-site handoff. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows :=
  not_faithfulRows_of_missingRegularXiZero C
    (missingRegularXiZero_of_nonrealRegularXiZero C.spectralCarrier hz hzim)

/-- Existence of an arithmetic-site carrier with all handoff rows. -/
def HasFaithfulArithmeticSiteCarrier : Prop :=
  exists C : Carrier.{u}, C.FaithfulRows

/-- A faithful arithmetic-site carrier supplies the Deninger handoff. -/
theorem hasPolarizedFaithfulDictionary_of_hasFaithfulArithmeticSiteCarrier
    (hC : HasFaithfulArithmeticSiteCarrier.{u}) :
    HasPolarizedFaithfulDictionary.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.spectralCarrier, polarizedFaithfulDictionary_of_faithfulRows C hrows⟩

/--
Circular calibration: any already faithful Deninger carrier can be relabeled as
an arithmetic-site carrier.

This deliberately uses `True` for the Frobenius row and reuses the existing
polarization and dictionary rows.  It is a calibration, not a construction of
the missing arithmetic-site geometry.
-/
def arithmeticSiteCarrierOfPolarizedCarrier
    (D : PolarizedSpectralCarrier.{u}) :
    Carrier.{u} where
  Site := D.Spectrum
  frobeniusLifts := True
  hodgeIndexPackage := D.carrierPolarized
  lefschetzTraceFormula := D.zeroDictionary
  spectralCarrier := D
  carrierPolarized_of_hodgeIndex := by
    intro hpolarized
    exact hpolarized
  zeroDictionary_of_lefschetz := by
    intro hdict
    exact hdict

/-- The calibrated arithmetic-site wrapper is faithful when the Deninger handoff is. -/
theorem faithfulRows_arithmeticSiteCarrierOfPolarizedFaithfulDictionary
    (D : PolarizedSpectralCarrier.{u})
    (h : PolarizedFaithfulDictionary D) :
    (arithmeticSiteCarrierOfPolarizedCarrier D).FaithfulRows :=
  ⟨trivial, h.1, h.2⟩

/-- A faithful Deninger handoff supplies the calibrated arithmetic-site carrier. -/
theorem hasFaithfulArithmeticSiteCarrier_of_hasPolarizedFaithfulDictionary
    (hD : HasPolarizedFaithfulDictionary.{u}) :
    HasFaithfulArithmeticSiteCarrier.{u} := by
  rcases hD with ⟨D, hfaithful⟩
  exact ⟨arithmeticSiteCarrierOfPolarizedCarrier D,
    faithfulRows_arithmeticSiteCarrierOfPolarizedFaithfulDictionary D hfaithful⟩

/--
The arithmetic-site handoff has exactly the same strength as the existing
Deninger faithful dictionary interface.

The reverse direction is the circular calibration above; it does not construct
Frobenius lifts, an arithmetic intersection form, or a Hodge-index theorem.
-/
theorem hasFaithfulArithmeticSiteCarrier_iff_hasPolarizedFaithfulDictionary :
    HasFaithfulArithmeticSiteCarrier.{u} ↔
      HasPolarizedFaithfulDictionary.{u} := by
  constructor
  · exact hasPolarizedFaithfulDictionary_of_hasFaithfulArithmeticSiteCarrier
  · exact hasFaithfulArithmeticSiteCarrier_of_hasPolarizedFaithfulDictionary

/--
At universe zero, the arithmetic-site handoff has exactly RH strength.

The useful direction is the conditional arithmetic-site proof route.  The
reverse direction is only the tautological spectral/dictionary calibration.
-/
theorem hasFaithfulArithmeticSiteCarrier_iff_riemannHypothesis :
    HasFaithfulArithmeticSiteCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulArithmeticSiteCarrier_iff_hasPolarizedFaithfulDictionary.trans
    hasPolarizedFaithfulDictionary_iff_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful arithmetic-site carrier. -/
theorem not_hasFaithfulArithmeticSiteCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulArithmeticSiteCarrier.{u} := by
  intro hC
  exact not_hasPolarizedFaithfulDictionary_of_nonrealRegularXiZero hz hzim
    (hasPolarizedFaithfulDictionary_of_hasFaithfulArithmeticSiteCarrier hC)

/-- Packaged conditional certificate for the arithmetic-site route. -/
structure ArithmeticSiteRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace ArithmeticSiteRHCertificate

/-- The packaged arithmetic-site certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : ArithmeticSiteRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_faithfulRows C.carrier C.faithfulRows

/-- The packaged arithmetic-site certificate supplies the Deninger handoff. -/
theorem hasPolarizedFaithfulDictionary
    (C : ArithmeticSiteRHCertificate.{u}) :
    HasPolarizedFaithfulDictionary.{u} :=
  ⟨C.carrier.spectralCarrier,
    polarizedFaithfulDictionary_of_faithfulRows C.carrier C.faithfulRows⟩

end ArithmeticSiteRHCertificate

end ArithmeticSiteCarrier
end JensenLadder
