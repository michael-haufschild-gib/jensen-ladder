import JensenLadder.DeningerCarrier

/-!
# Complex spectral determinant carrier boundary

This module separates two often-conflated spectral claims.

* A complex spectral/determinant dictionary for the regular `Xi` zeros is
  tautological: take the spectrum to be the zero set itself.
* A real-line or polarized spectral dictionary is RH-strength.  To hand off to
  the existing Hilbert--Polya/Deninger endpoint, the complex spectrum must be
  line-centered by an external theorem, not by postselection.

This is the Lean-facing boundary for non-self-adjoint determinant routes,
Connes/Meyer-style complex spectra, and zero-space models.  It does not
construct a self-adjoint operator, a Deninger cohomology, a determinant
identity, or RH.  It records exactly which row upgrades a complex determinant
identity into the existing real spectral endpoint.

Evidence class: formal/certificate artifact and dead-end elimination.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ComplexSpectralDeterminantCarrier

open SpectralRealization

universe u

/-- Soundness of a complex spectral model for the regular `Xi` zeros. -/
def ComplexRegularXiZeroSoundness {Spectrum : Type u}
    (eigenvalue : Spectrum -> ℂ) : Prop :=
  ∀ γ : Spectrum, RHReduction.riemannXiRegularZero (eigenvalue γ)

/-- Completeness of a complex spectral model for the regular `Xi` zeros. -/
def ComplexRegularXiZeroCompleteness {Spectrum : Type u}
    (eigenvalue : Spectrum -> ℂ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
    ∃ γ : Spectrum, z = eigenvalue γ

/-- Exactness of a complex spectral model for the regular `Xi` zeros. -/
def ComplexRegularXiZeroExact {Spectrum : Type u}
    (eigenvalue : Spectrum -> ℂ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ↔
    ∃ γ : Spectrum, z = eigenvalue γ

/-- Soundness plus completeness is exactness for a complex zero dictionary. -/
theorem complexRegularXiZeroExact_of_sound_complete
    {Spectrum : Type u} {eigenvalue : Spectrum -> ℂ}
    (hsound : ComplexRegularXiZeroSoundness eigenvalue)
    (hcomplete : ComplexRegularXiZeroCompleteness eigenvalue) :
    ComplexRegularXiZeroExact eigenvalue := by
  intro z
  constructor
  · exact hcomplete z
  · rintro ⟨γ, rfl⟩
    exact hsound γ

/--
A complex determinant/spectral carrier.

`sourceNativeOperator` and `complexDeterminantIdentity` are deliberately weak:
they can name an exact non-self-adjoint determinant construction without
asserting line-centering.  The load-bearing row for Hilbert--Polya is
`lineCenteredSpectrum`, whose adapter must prove that all complex eigenvalues
have imaginary part zero in the `Xi` variable.
-/
structure Carrier where
  Spectrum : Type u
  eigenvalue : Spectrum -> ℂ
  sourceNativeOperator : Prop
  complexDeterminantIdentity : Prop
  regularZeroDictionary : Prop
  lineCenteredSpectrum : Prop
  fakeFamilyRejection : Prop
  sound_of_dictionary :
    regularZeroDictionary -> ComplexRegularXiZeroSoundness eigenvalue
  complete_of_dictionary :
    regularZeroDictionary -> ComplexRegularXiZeroCompleteness eigenvalue
  lineCentered_of_row :
    lineCenteredSpectrum -> ∀ γ : Spectrum, (eigenvalue γ).im = 0

/-- The real height obtained by forgetting the zero imaginary part. -/
def Carrier.realHeight (C : Carrier.{u}) (γ : C.Spectrum) : ℝ :=
  (C.eigenvalue γ).re

/-- Source-native complex determinant rows before any real-line theorem. -/
def Carrier.DeterminantRows (C : Carrier.{u}) : Prop :=
  C.sourceNativeOperator ∧ C.complexDeterminantIdentity

/-- Complex determinant plus exact zero-dictionary rows. -/
def Carrier.ComplexRows (C : Carrier.{u}) : Prop :=
  C.DeterminantRows ∧ C.regularZeroDictionary

/-- The real-line row needed to make the complex spectrum a Hilbert--Polya endpoint. -/
def Carrier.LineCenteredRows (C : Carrier.{u}) : Prop :=
  C.lineCenteredSpectrum

/-- Full rows for the complex spectral carrier handoff. -/
def Carrier.FaithfulRows (C : Carrier.{u}) : Prop :=
  C.ComplexRows ∧ C.LineCenteredRows ∧ C.fakeFamilyRejection

namespace Carrier

/-- A line-centered eigenvalue equals its real-height embedding. -/
theorem realHeight_cast_eq_eigenvalue
    (C : Carrier.{u}) (hline : C.LineCenteredRows) (γ : C.Spectrum) :
    ((C.realHeight γ : ℝ) : ℂ) = C.eigenvalue γ := by
  apply Complex.ext
  · simp [realHeight]
  · simp [realHeight, C.lineCentered_of_row hline γ]

/-- A complex dictionary plus line-centering gives real-height soundness. -/
theorem regularXiZeroSoundness_of_dictionary_lineCentered
    (C : Carrier.{u}) (hdict : C.regularZeroDictionary)
    (hline : C.LineCenteredRows) :
    RegularXiZeroSoundness C.realHeight := by
  intro γ
  have hreg : RHReduction.riemannXiRegularZero (C.eigenvalue γ) :=
    C.sound_of_dictionary hdict γ
  have hcast : ((C.realHeight γ : ℝ) : ℂ) = C.eigenvalue γ :=
    C.realHeight_cast_eq_eigenvalue hline γ
  simpa [hcast] using hreg

/-- A complex dictionary plus line-centering gives real-height completeness. -/
theorem regularXiZeroCompleteness_of_dictionary_lineCentered
    (C : Carrier.{u}) (hdict : C.regularZeroDictionary)
    (hline : C.LineCenteredRows) :
    RegularXiZeroCompleteness C.realHeight := by
  intro z hz
  rcases C.complete_of_dictionary hdict z hz with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  rw [C.realHeight_cast_eq_eigenvalue hline γ]
  exact hγ

/-- Full rows supply the existing exact regular real spectral realization. -/
def regularSpectralRealization_of_faithfulRows
    (C : Carrier.{u}) (h : C.FaithfulRows) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := C.Spectrum
  height := C.realHeight
  sound :=
    C.regularXiZeroSoundness_of_dictionary_lineCentered h.1.2 h.2.1
  complete :=
    C.regularXiZeroCompleteness_of_dictionary_lineCentered h.1.2 h.2.1

/-- Full rows prove mathlib's `RiemannHypothesis` through the real endpoint. -/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u}) (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (C.regularSpectralRealization_of_faithfulRows h)

/-- Full rows also supply the Deninger faithful dictionary handoff. -/
theorem hasPolarizedFaithfulDictionary_of_faithfulRows
    (C : Carrier.{u}) (h : C.FaithfulRows) :
    DeningerCarrier.HasPolarizedFaithfulDictionary.{u} :=
  DeningerCarrier.hasPolarizedFaithfulDictionary_of_regularSpectralRealization
    (C.regularSpectralRealization_of_faithfulRows h)

/--
A non-real regular `Xi` zero blocks the line-centered row of any exact complex
zero dictionary.
-/
theorem not_lineCenteredRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0)
    (hdict : C.regularZeroDictionary) :
    ¬ C.LineCenteredRows := by
  intro hline
  rcases C.complete_of_dictionary hdict z hz with ⟨γ, hγ⟩
  exact hzim (by
    rw [hγ]
    exact C.lineCentered_of_row hline γ)

/-- A non-real regular `Xi` zero blocks the full faithful handoff. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows := by
  intro hrows
  exact C.not_lineCenteredRows_of_nonrealRegularXiZero hz hzim hrows.1.2 hrows.2.1

end Carrier

/--
The canonical complex zero carrier: take the spectrum to be the regular zero
set itself.  This gives an exact complex dictionary with no spectral theorem.

Its line-centered row is precisely the RH-strength assertion that all regular
zeros are real.
-/
noncomputable def canonicalComplexZeroCarrier : Carrier.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXiRegularZero z}
  eigenvalue := fun γ => γ.1
  sourceNativeOperator := True
  complexDeterminantIdentity := True
  regularZeroDictionary := True
  lineCenteredSpectrum :=
    ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z}, γ.1.im = 0
  fakeFamilyRejection := True
  sound_of_dictionary := by
    intro _h γ
    exact γ.2
  complete_of_dictionary := by
    intro _h z hz
    exact ⟨⟨z, hz⟩, rfl⟩
  lineCentered_of_row := by
    intro hline γ
    exact hline γ

/-- The canonical complex carrier has the weak complex rows unconditionally. -/
theorem canonicalComplexZeroCarrier_complexRows :
    canonicalComplexZeroCarrier.ComplexRows :=
  ⟨⟨trivial, trivial⟩, trivial⟩

/--
The line-centered row of the canonical complex zero carrier is exactly
mathlib's `RiemannHypothesis`.

The reverse direction is tautological and circular as a proof method.
-/
theorem canonicalComplexZeroCarrier_lineCenteredRows_iff_riemannHypothesis :
    canonicalComplexZeroCarrier.LineCenteredRows ↔ RiemannHypothesis := by
  constructor
  · intro hline
    exact (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
      (by
        intro z hz
        change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
          γ.1.im = 0 at hline
        exact hline ⟨z, hz⟩)
  · intro hRH
    change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
      γ.1.im = 0
    intro γ
    exact (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      hRH γ.1 γ.2

/-- A non-real regular zero makes the canonical complex carrier non-line-centered. -/
theorem not_canonicalComplexZeroCarrier_lineCenteredRows_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ canonicalComplexZeroCarrier.LineCenteredRows := by
  intro hline
  change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
    γ.1.im = 0 at hline
  exact hzim (hline ⟨z, hz⟩)

/--
If RH is false via a non-real regular zero, then an exact complex zero
dictionary still exists but cannot supply the line-centered row.
-/
theorem complexRows_do_not_supply_lineCenteredRows_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ∃ C : Carrier.{0}, C.ComplexRows ∧ ¬ C.LineCenteredRows :=
  ⟨canonicalComplexZeroCarrier, canonicalComplexZeroCarrier_complexRows,
    not_canonicalComplexZeroCarrier_lineCenteredRows_of_nonrealRegularXiZero
      hz hzim⟩

/-- A dummy determinant carrier: determinant-shaped rows without any zero dictionary. -/
def dummyDeterminantCarrier : Carrier.{0} where
  Spectrum := PUnit
  eigenvalue := fun _ => Complex.I
  sourceNativeOperator := True
  complexDeterminantIdentity := True
  regularZeroDictionary := False
  lineCenteredSpectrum := False
  fakeFamilyRejection := True
  sound_of_dictionary := by
    intro hdict
    cases hdict
  complete_of_dictionary := by
    intro hdict
    cases hdict
  lineCentered_of_row := by
    intro hline
    cases hline

/-- Determinant-shaped rows alone do not supply the zero dictionary. -/
theorem determinantRows_do_not_supply_complexRows :
    ∃ C : Carrier.{0}, C.DeterminantRows ∧ ¬ C.ComplexRows :=
  ⟨dummyDeterminantCarrier, ⟨trivial, trivial⟩, by
    intro hrows
    exact hrows.2⟩

/-- Determinant-shaped rows alone do not supply the faithful real-spectrum handoff. -/
theorem determinantRows_do_not_supply_faithfulRows :
    ∃ C : Carrier.{0}, C.DeterminantRows ∧ ¬ C.FaithfulRows :=
  ⟨dummyDeterminantCarrier, ⟨trivial, trivial⟩, by
    intro hrows
    exact hrows.1.2⟩

/-- Existence of a faithful complex spectral carrier. -/
def HasFaithfulComplexSpectralCarrier : Prop :=
  ∃ C : Carrier.{u}, C.FaithfulRows

/-- A faithful complex spectral carrier proves RH. -/
theorem riemannHypothesis_of_hasFaithfulComplexSpectralCarrier
    (hC : HasFaithfulComplexSpectralCarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_faithfulRows hrows

/-- RH supplies the canonical faithful complex carrier, tautologically. -/
theorem hasFaithfulComplexSpectralCarrier_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    HasFaithfulComplexSpectralCarrier.{0} := by
  refine ⟨canonicalComplexZeroCarrier, ?_⟩
  exact ⟨canonicalComplexZeroCarrier_complexRows,
    (canonicalComplexZeroCarrier_lineCenteredRows_iff_riemannHypothesis).2 hRH,
    trivial⟩

/--
At universe zero, the faithful complex spectral interface is exactly RH
strength.  The reverse direction is the tautological zero-set carrier and is
not an anti-circular construction.
-/
theorem hasFaithfulComplexSpectralCarrier_iff_riemannHypothesis :
    HasFaithfulComplexSpectralCarrier.{0} ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_hasFaithfulComplexSpectralCarrier
  · exact hasFaithfulComplexSpectralCarrier_of_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful complex spectral carrier. -/
theorem not_hasFaithfulComplexSpectralCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulComplexSpectralCarrier.{u} := by
  intro hC
  exact DeningerCarrier.not_hasPolarizedFaithfulDictionary_of_nonrealRegularXiZero
    hz hzim
    (by
      rcases hC with ⟨C, hrows⟩
      exact C.hasPolarizedFaithfulDictionary_of_faithfulRows hrows)

end ComplexSpectralDeterminantCarrier
end JensenLadder
