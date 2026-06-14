import JensenLadder.SpectralRealization

/-!
# Unitary cokernel carrier boundary

This file records the Lean-facing boundary for the Connes/scaling-unitary
route.  A unitary scaling action, or a cokernel/absorption quotient marker, is
not by itself a spectral realization of the `Xi` zeros.  The load-bearing row is
the exact spectral-identification theorem: the real cokernel phases must supply
soundness and completeness for the regular `Xi` zero set.

This module does not construct an adele class space, a spectral triple, a
quotient Hilbert space, a self-adjoint operator, a determinant convergence
theorem, or RH.  It only names the exact interface row that such a construction
must deliver.

Evidence class: formal/certificate artifact + dead-end-boundary calibration.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace UnitaryCokernelCarrier

open SpectralRealization

universe u

/--
A scaling-unitary/cokernel spectral carrier candidate.

`scalingActionUnitary` records the manifest-unitarity part of the route.
`cokernelQuotient` records the absorption/cokernel quotient that is supposed to
turn continuous scaling data into the relevant point spectrum.  Neither row is
used directly to prove RH below.  The formal handoff is the
`spectralIdentification` row together with its adapters into the existing
regular `Xi` zero soundness and completeness predicates.
-/
structure Carrier where
  Spectrum : Type u
  phase : Spectrum -> ℝ
  scalingActionUnitary : Prop
  cokernelQuotient : Prop
  spectralIdentification : Prop
  sound_of_spectralIdentification :
    spectralIdentification -> RegularXiZeroSoundness phase
  complete_of_spectralIdentification :
    spectralIdentification -> RegularXiZeroCompleteness phase

namespace Carrier

/-- The unitary/cokernel bookkeeping rows alone. -/
def UnitaryRows (C : Carrier.{u}) : Prop :=
  C.scalingActionUnitary ∧ C.cokernelQuotient

/--
The full faithful handoff for the unitary-cokernel route.

The first component records the intended unitary quotient shape.  The second
component is the load-bearing exact spectral-identification row.
-/
def FaithfulRows (C : Carrier.{u}) : Prop :=
  C.UnitaryRows ∧ C.spectralIdentification

/-- A regular `Xi` zero not represented by the carrier's real phases. -/
def MissingRegularXiZero (C : Carrier.{u}) : Prop :=
  ∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧
    ∀ γ : C.Spectrum, z ≠ (C.phase γ : ℂ)

/-- Spectral identification supplies the existing exact regular spectral endpoint. -/
def regularSpectralRealization_of_spectralIdentification
    (C : Carrier.{u})
    (hid : C.spectralIdentification) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := C.Spectrum
  height := C.phase
  sound := C.sound_of_spectralIdentification hid
  complete := C.complete_of_spectralIdentification hid

/-- Faithful unitary-cokernel rows supply the existing exact regular spectral endpoint. -/
def regularSpectralRealization_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannXiRegularSpectralRealization.{u} :=
  regularSpectralRealization_of_spectralIdentification C h.2

/--
A non-circular unitary-cokernel carrier with exact spectral identification would
prove mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_spectralIdentification
    (C : Carrier.{u})
    (hid : C.spectralIdentification) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_spectralIdentification C hid)

/-- Faithful unitary-cokernel rows prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_spectralIdentification C h.2

/-- Spectral identification rules out missing regular `Xi` zeros. -/
theorem no_missingRegularXiZero_of_spectralIdentification
    (C : Carrier.{u})
    (hid : C.spectralIdentification) :
    ¬ C.MissingRegularXiZero := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases C.complete_of_spectralIdentification hid z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missing regular zero falsifies the spectral-identification row. -/
theorem not_spectralIdentification_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : C.MissingRegularXiZero) :
    ¬ C.spectralIdentification := by
  intro hid
  exact no_missingRegularXiZero_of_spectralIdentification C hid hmiss

/-- A missing regular zero blocks the full faithful handoff. -/
theorem not_faithfulRows_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : C.MissingRegularXiZero) :
    ¬ C.FaithfulRows := by
  intro h
  exact not_spectralIdentification_of_missingRegularXiZero C hmiss h.2

/-- A non-real regular `Xi` zero is missing from every real-phase carrier. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    C.MissingRegularXiZero := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (by
    rw [hγ]
    simp)

/-- A non-real regular `Xi` zero falsifies spectral identification. -/
theorem not_spectralIdentification_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.spectralIdentification :=
  not_spectralIdentification_of_missingRegularXiZero C
    (missingRegularXiZero_of_nonrealRegularXiZero C hz hzim)

/-- A non-real regular `Xi` zero blocks faithful unitary-cokernel rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows :=
  not_faithfulRows_of_missingRegularXiZero C
    (missingRegularXiZero_of_nonrealRegularXiZero C hz hzim)

end Carrier

/--
A dummy carrier showing that the abstract unitary/cokernel bookkeeping rows do
not themselves contain spectral identification.

This is only interface hygiene: it is not a theorem about genuine unitary
representations or Connes' adele class space.
-/
def emptyUnitaryCokernelCarrier : Carrier.{0} where
  Spectrum := Empty
  phase := fun γ => nomatch γ
  scalingActionUnitary := True
  cokernelQuotient := True
  spectralIdentification := False
  sound_of_spectralIdentification := by
    intro hfalse
    cases hfalse
  complete_of_spectralIdentification := by
    intro hfalse
    cases hfalse

/-- The dummy carrier has the unitary/cokernel bookkeeping rows. -/
theorem emptyUnitaryCokernelCarrier_unitaryRows :
    emptyUnitaryCokernelCarrier.UnitaryRows :=
  ⟨trivial, trivial⟩

/-- The dummy carrier deliberately has no spectral-identification row. -/
theorem emptyUnitaryCokernelCarrier_not_spectralIdentification :
    ¬ emptyUnitaryCokernelCarrier.spectralIdentification := by
  intro hfalse
  exact hfalse

/--
At the abstract interface level, unitary/cokernel bookkeeping rows alone do not
supply spectral identification.
-/
theorem unitaryRows_do_not_supply_spectralIdentification :
    ∃ C : Carrier.{0}, C.UnitaryRows ∧ ¬ C.spectralIdentification :=
  ⟨emptyUnitaryCokernelCarrier,
    emptyUnitaryCokernelCarrier_unitaryRows,
    emptyUnitaryCokernelCarrier_not_spectralIdentification⟩

/-- Existence of a faithful unitary-cokernel carrier at a fixed universe level. -/
def HasFaithfulUnitaryCokernelCarrier : Prop :=
  ∃ C : Carrier.{u}, C.FaithfulRows

/-- A non-real regular `Xi` zero rules out every faithful unitary-cokernel carrier. -/
theorem not_hasFaithfulUnitaryCokernelCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulUnitaryCokernelCarrier.{u} := by
  rintro ⟨C, h⟩
  exact C.not_faithfulRows_of_nonrealRegularXiZero hz hzim h

/--
The tautological unitary-cokernel carrier obtained from an already exact regular
spectral realization.

This is deliberately circular as a proof method.  It labels the already exact
spectral realization with `True` unitary/cokernel markers, so it is only a
calibration of endpoint strength.
-/
def unitaryCokernelCarrierOfRegularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    Carrier.{u} where
  Spectrum := S.Spectrum
  phase := S.height
  scalingActionUnitary := True
  cokernelQuotient := True
  spectralIdentification := True
  sound_of_spectralIdentification := by
    intro _h
    exact S.sound
  complete_of_spectralIdentification := by
    intro _h
    exact S.complete

/-- An exact regular spectral realization supplies calibrated faithful rows. -/
theorem faithfulRows_unitaryCokernelCarrierOfRegularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    (unitaryCokernelCarrierOfRegularSpectralRealization S).FaithfulRows :=
  ⟨⟨trivial, trivial⟩, trivial⟩

/-- An exact regular spectral realization gives a faithful unitary-cokernel carrier. -/
theorem hasFaithfulUnitaryCokernelCarrier_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization.{u}) :
    HasFaithfulUnitaryCokernelCarrier.{u} :=
  ⟨unitaryCokernelCarrierOfRegularSpectralRealization S,
    faithfulRows_unitaryCokernelCarrierOfRegularSpectralRealization S⟩

/-- A faithful unitary-cokernel carrier gives a nonempty exact spectral realization. -/
theorem nonempty_regularSpectralRealization_of_hasFaithfulUnitaryCokernelCarrier
    (hC : HasFaithfulUnitaryCokernelCarrier.{u}) :
    Nonempty RiemannXiRegularSpectralRealization.{u} := by
  rcases hC with ⟨C, h⟩
  exact ⟨C.regularSpectralRealization_of_faithfulRows h⟩

/--
The faithful unitary-cokernel handoff is exactly the existing regular spectral
endpoint.  The reverse direction is the tautological calibration above, not a
construction of the scaling/cokernel operator.
-/
theorem hasFaithfulUnitaryCokernelCarrier_iff_regularSpectralRealization :
    HasFaithfulUnitaryCokernelCarrier.{u} ↔
      Nonempty RiemannXiRegularSpectralRealization.{u} := by
  constructor
  · exact nonempty_regularSpectralRealization_of_hasFaithfulUnitaryCokernelCarrier
  · intro hS
    rcases hS with ⟨S⟩
    exact hasFaithfulUnitaryCokernelCarrier_of_regularSpectralRealization S

/-- At universe zero, the faithful unitary-cokernel endpoint has exactly RH strength. -/
theorem hasFaithfulUnitaryCokernelCarrier_iff_riemannHypothesis :
    HasFaithfulUnitaryCokernelCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulUnitaryCokernelCarrier_iff_regularSpectralRealization.trans
    nonempty_regularSpectralRealization_iff_riemannHypothesis

/-- Packaged conditional certificate for the unitary-cokernel route. -/
structure UnitaryCokernelRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace UnitaryCokernelRHCertificate

/-- The packaged certificate supplies the existing exact regular spectral endpoint. -/
def regularSpectralRealization
    (C : UnitaryCokernelRHCertificate.{u}) :
    RiemannXiRegularSpectralRealization.{u} :=
  C.carrier.regularSpectralRealization_of_faithfulRows C.faithfulRows

/-- The packaged unitary-cokernel certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : UnitaryCokernelRHCertificate.{u}) :
    RiemannHypothesis :=
  C.carrier.riemannHypothesis_of_faithfulRows C.faithfulRows

end UnitaryCokernelRHCertificate

end UnitaryCokernelCarrier
end JensenLadder
