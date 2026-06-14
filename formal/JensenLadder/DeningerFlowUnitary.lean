import JensenLadder.DeningerCarrier

/-!
# Deninger flow-unitarity carrier boundary

This module records the flow-level split in the Deninger/cohomological route.

The conditional Deninger theorem has two logically distinct parts:

* a polarization/normalized-unitarity package, which is the Hodge-index input
  that makes the degree-one flow have real centered spectral heights;
* a determinant/trace/regularity package, which identifies those real heights
  with *all* regular `Xi` zeros.

The first part is the geometric positivity/reality mechanism.  The second part
is the spectral-faithfulness row where RH-strength enters.  This file names the
rows and proves their handoff to the existing `DeningerCarrier` endpoint.

It does not construct Deninger's cohomology, prove unitarity from a
polarization, prove a determinant identity, prove a trace formula, or prove RH.

Evidence class: formal/certificate artifact + dead-end-boundary calibration.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace DeningerFlowUnitary

open SpectralRealization

universe u

/--
A Deninger-style flow carrier with the reality rows separated from the
faithfulness rows.

`polarizedCohomology`, `normalizedFlowUnitary`, and `spectralRegularity` are
the flow-reality rows from the conditional Deninger theorem.  They do not, by
themselves, identify the spectrum with the `Xi` zeros.  The load-bearing
faithfulness row is the determinant/trace identity as consumed by
`zeroDictionary_of_determinant`.
-/
structure FlowCarrier where
  Spectrum : Type u
  height : Spectrum -> ℝ
  polarizedCohomology : Prop
  normalizedFlowUnitary : Prop
  spectralRegularity : Prop
  determinantIdentity : Prop
  zeroDictionary : Prop
  zeroDictionary_of_determinant :
    determinantIdentity -> spectralRegularity -> zeroDictionary
  sound_of_zeroDictionary :
    zeroDictionary -> RegularXiZeroSoundness height
  complete_of_zeroDictionary :
    zeroDictionary -> RegularXiZeroCompleteness height

namespace FlowCarrier

/--
Rows that explain why the candidate spectrum is real-centered.

These are necessary Deninger/Hodge rows, but they are not the exact
spectral-identification theorem.
-/
def RealityRows (C : FlowCarrier.{u}) : Prop :=
  C.polarizedCohomology ∧ C.normalizedFlowUnitary ∧ C.spectralRegularity

/-- Full rows needed for the Deninger-flow handoff. -/
def FaithfulRows (C : FlowCarrier.{u}) : Prop :=
  C.RealityRows ∧ C.determinantIdentity

/-- Faithful rows supply the zero dictionary. -/
theorem zeroDictionary_of_faithfulRows
    (C : FlowCarrier.{u})
    (h : C.FaithfulRows) :
    C.zeroDictionary :=
  C.zeroDictionary_of_determinant h.2 h.1.2.2

/-- Collapse the flow-level carrier to the existing polarized spectral carrier. -/
def polarizedSpectralCarrier
    (C : FlowCarrier.{u}) :
    DeningerCarrier.PolarizedSpectralCarrier.{u} where
  Spectrum := C.Spectrum
  height := C.height
  carrierPolarized := C.RealityRows
  zeroDictionary := C.zeroDictionary
  sound_of_dictionary := C.sound_of_zeroDictionary
  complete_of_dictionary := C.complete_of_zeroDictionary

/-- Faithful flow rows supply the existing Deninger faithful dictionary. -/
theorem polarizedFaithfulDictionary_of_faithfulRows
    (C : FlowCarrier.{u})
    (h : C.FaithfulRows) :
    DeningerCarrier.PolarizedFaithfulDictionary C.polarizedSpectralCarrier :=
  ⟨h.1, C.zeroDictionary_of_faithfulRows h⟩

/-- Faithful Deninger flow rows prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_faithfulRows
    (C : FlowCarrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  DeningerCarrier.riemannHypothesis_of_polarizedFaithfulDictionary
    C.polarizedSpectralCarrier
    (C.polarizedFaithfulDictionary_of_faithfulRows h)

/-- A regular `Xi` zero not represented by the flow carrier's real heights. -/
def MissingRegularXiZero (C : FlowCarrier.{u}) : Prop :=
  exists z : ℂ, RHReduction.riemannXiRegularZero z ∧
    forall γ : C.Spectrum, z ≠ (C.height γ : ℂ)

/-- The zero dictionary rules out unrepresented regular zeros. -/
theorem no_missingRegularXiZero_of_zeroDictionary
    (C : FlowCarrier.{u})
    (hdict : C.zeroDictionary) :
    ¬ C.MissingRegularXiZero := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases C.complete_of_zeroDictionary hdict z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missing regular zero blocks the zero dictionary. -/
theorem not_zeroDictionary_of_missingRegularXiZero
    (C : FlowCarrier.{u})
    (hmiss : C.MissingRegularXiZero) :
    ¬ C.zeroDictionary := by
  intro hdict
  exact C.no_missingRegularXiZero_of_zeroDictionary hdict hmiss

/-- A missing regular zero blocks faithful flow rows. -/
theorem not_faithfulRows_of_missingRegularXiZero
    (C : FlowCarrier.{u})
    (hmiss : C.MissingRegularXiZero) :
    ¬ C.FaithfulRows := by
  intro h
  exact C.not_zeroDictionary_of_missingRegularXiZero hmiss
    (C.zeroDictionary_of_faithfulRows h)

/-- A non-real regular `Xi` zero is missing from every real-height flow carrier. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (C : FlowCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    C.MissingRegularXiZero := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (by
    rw [hγ]
    simp)

/-- A non-real regular `Xi` zero blocks faithful flow rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : FlowCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows :=
  C.not_faithfulRows_of_missingRegularXiZero
    (C.missingRegularXiZero_of_nonrealRegularXiZero hz hzim)

end FlowCarrier

/--
A dummy flow carrier showing that polarization/unitarity/regularity rows alone
do not supply the determinant/zero-dictionary row.

This is only interface hygiene: it is not a theorem about genuine Deninger
cohomology.
-/
def emptyRealityFlowCarrier : FlowCarrier.{0} where
  Spectrum := Empty
  height := fun γ => nomatch γ
  polarizedCohomology := True
  normalizedFlowUnitary := True
  spectralRegularity := True
  determinantIdentity := False
  zeroDictionary := False
  zeroDictionary_of_determinant := by
    intro hfalse
    cases hfalse
  sound_of_zeroDictionary := by
    intro hfalse
    cases hfalse
  complete_of_zeroDictionary := by
    intro hfalse
    cases hfalse

/-- The dummy carrier satisfies all flow-reality rows. -/
theorem emptyRealityFlowCarrier_realityRows :
    emptyRealityFlowCarrier.RealityRows :=
  ⟨trivial, trivial, trivial⟩

/-- The dummy carrier deliberately has no zero dictionary. -/
theorem emptyRealityFlowCarrier_not_zeroDictionary :
    ¬ emptyRealityFlowCarrier.zeroDictionary := by
  intro hfalse
  exact hfalse

/--
Flow-reality rows alone do not imply the zero-dictionary row.

The determinant/trace faithfulness theorem is a separate obligation.
-/
theorem realityRows_do_not_supply_zeroDictionary :
    exists C : FlowCarrier.{0}, C.RealityRows ∧ ¬ C.zeroDictionary :=
  ⟨emptyRealityFlowCarrier,
    emptyRealityFlowCarrier_realityRows,
    emptyRealityFlowCarrier_not_zeroDictionary⟩

/-- Flow-reality rows alone do not imply faithful flow rows. -/
theorem realityRows_do_not_supply_faithfulRows :
    exists C : FlowCarrier.{0}, C.RealityRows ∧ ¬ C.FaithfulRows := by
  refine ⟨emptyRealityFlowCarrier, emptyRealityFlowCarrier_realityRows, ?_⟩
  intro h
  exact h.2

/-- Existence of a faithful Deninger flow carrier. -/
def HasFaithfulDeningerFlowCarrier : Prop :=
  exists C : FlowCarrier.{u}, C.FaithfulRows

/-- A faithful flow carrier supplies the existing Deninger carrier handoff. -/
theorem hasPolarizedFaithfulDictionary_of_hasFaithfulDeningerFlowCarrier
    (hC : HasFaithfulDeningerFlowCarrier.{u}) :
    DeningerCarrier.HasPolarizedFaithfulDictionary.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.polarizedSpectralCarrier,
    C.polarizedFaithfulDictionary_of_faithfulRows hrows⟩

/--
Circular calibration: any already faithful Deninger carrier can be relabeled as
a flow-unitarity carrier.

This uses `True` for the normalized-unitarity and regularity rows and reuses the
existing dictionary row.  It is not a construction of Deninger's cohomology or
the unitary normalized flow.
-/
def flowCarrierOfPolarizedSpectralCarrier
    (D : DeningerCarrier.PolarizedSpectralCarrier.{u}) :
    FlowCarrier.{u} where
  Spectrum := D.Spectrum
  height := D.height
  polarizedCohomology := D.carrierPolarized
  normalizedFlowUnitary := True
  spectralRegularity := True
  determinantIdentity := D.zeroDictionary
  zeroDictionary := D.zeroDictionary
  zeroDictionary_of_determinant := by
    intro hdict _hregular
    exact hdict
  sound_of_zeroDictionary := D.sound_of_dictionary
  complete_of_zeroDictionary := D.complete_of_dictionary

/-- The calibrated flow wrapper is faithful when the Deninger carrier is. -/
theorem faithfulRows_flowCarrierOfPolarizedFaithfulDictionary
    (D : DeningerCarrier.PolarizedSpectralCarrier.{u})
    (h : DeningerCarrier.PolarizedFaithfulDictionary D) :
    (flowCarrierOfPolarizedSpectralCarrier D).FaithfulRows :=
  ⟨⟨h.1, trivial, trivial⟩, h.2⟩

/-- A faithful Deninger carrier supplies the calibrated flow carrier. -/
theorem hasFaithfulDeningerFlowCarrier_of_hasPolarizedFaithfulDictionary
    (hD : DeningerCarrier.HasPolarizedFaithfulDictionary.{u}) :
    HasFaithfulDeningerFlowCarrier.{u} := by
  rcases hD with ⟨D, hfaithful⟩
  exact ⟨flowCarrierOfPolarizedSpectralCarrier D,
    faithfulRows_flowCarrierOfPolarizedFaithfulDictionary D hfaithful⟩

/--
The faithful Deninger-flow handoff has exactly the same endpoint strength as
the existing faithful Deninger carrier.

The reverse direction is the circular calibration above; it does not construct
the missing flow-unitarity theorem.
-/
theorem hasFaithfulDeningerFlowCarrier_iff_hasPolarizedFaithfulDictionary :
    HasFaithfulDeningerFlowCarrier.{u} ↔
      DeningerCarrier.HasPolarizedFaithfulDictionary.{u} := by
  constructor
  · exact hasPolarizedFaithfulDictionary_of_hasFaithfulDeningerFlowCarrier
  · exact hasFaithfulDeningerFlowCarrier_of_hasPolarizedFaithfulDictionary

/--
At universe zero, the faithful Deninger-flow interface has exactly RH strength.

The useful direction is the conditional polarized-flow proof route.  The
reverse direction is only the tautological Deninger-carrier calibration.
-/
theorem hasFaithfulDeningerFlowCarrier_iff_riemannHypothesis :
    HasFaithfulDeningerFlowCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulDeningerFlowCarrier_iff_hasPolarizedFaithfulDictionary.trans
    DeningerCarrier.hasPolarizedFaithfulDictionary_iff_riemannHypothesis

/-- A faithful Deninger flow carrier proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_hasFaithfulDeningerFlowCarrier
    (hC : HasFaithfulDeningerFlowCarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_faithfulRows hrows

/-- A non-real regular `Xi` zero rules out every faithful Deninger flow carrier. -/
theorem not_hasFaithfulDeningerFlowCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulDeningerFlowCarrier.{u} := by
  rintro ⟨C, hrows⟩
  exact C.not_faithfulRows_of_nonrealRegularXiZero hz hzim hrows

/-- Packaged conditional certificate for the Deninger flow-unitarity route. -/
structure DeningerFlowRHCertificate where
  carrier : FlowCarrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace DeningerFlowRHCertificate

/-- The packaged flow certificate supplies the existing Deninger handoff. -/
theorem hasPolarizedFaithfulDictionary
    (C : DeningerFlowRHCertificate.{u}) :
    DeningerCarrier.HasPolarizedFaithfulDictionary.{u} :=
  ⟨C.carrier.polarizedSpectralCarrier,
    C.carrier.polarizedFaithfulDictionary_of_faithfulRows C.faithfulRows⟩

/-- The packaged flow certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : DeningerFlowRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_hasFaithfulDeningerFlowCarrier
    ⟨C.carrier, C.faithfulRows⟩

end DeningerFlowRHCertificate

end DeningerFlowUnitary
end JensenLadder
