import JensenLadder.SquaredVariablePullback

/-!
# Meyer Fork A squared determinant boundary

This module records the Lean-facing lesson of
`docs/rh/opus_forkA_squared_variable_determinant_20260614.md`.

Fork A works in the squared variable.  A Meyer-style source-native operator,
plus Schatten/determinant-class control, can at most give a complex squared
zero dictionary:

```text
  every regular Xi zero z has z^2 in the complex squared spectrum.
```

That determinant identity is RH-agnostic.  A Riesz-basis theorem is only one
possible sufficient route to trace class; it is not part of the abstract target.
There is also a Hilbert--Schmidt / Carleman-det2 branch with an explicit
genus-gauge constant.  Either way, the determinant-class identity becomes a
Hilbert--Polya/RH endpoint only after an additional metric/polarization row
identifies the squared spectrum with nonnegative real energies.  This is
exactly the row consumed by `SquaredVariablePullback`.

This file does not prove Meyer's theorem, Schatten-class control, Lidskii's
theorem, Carleman det2 theory, the explicit genus-gauge constant, the
order-`1/2` Hadamard product, or RH.  It only separates the RH-agnostic
determinant row from the RH-strength positive squared-spectrum row.

Evidence class: formal/certificate artifact and dead-end elimination.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace MeyerForkASquaredDeterminant

open SquaredVariablePullback

universe u

/-- Soundness of a complex squared-spectrum model for regular `Xi` zeros. -/
def ComplexSquaredSoundness {Spectrum : Type u}
    (energy : Spectrum -> ℂ) : Prop :=
  ∀ γ : Spectrum, ∃ z : ℂ,
    RHReduction.riemannXiRegularZero z ∧ energy γ = z ^ 2

/-- Completeness of a complex squared-spectrum model for regular `Xi` zeros. -/
def ComplexSquaredCompleteness {Spectrum : Type u}
    (energy : Spectrum -> ℂ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
    ∃ γ : Spectrum, z ^ 2 = energy γ

/-- Exactness of a complex squared-spectrum model for regular `Xi` zeros. -/
def ComplexSquaredExact {Spectrum : Type u}
    (energy : Spectrum -> ℂ) : Prop :=
  ∀ w : ℂ, (∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧ w = z ^ 2) ↔
    ∃ γ : Spectrum, w = energy γ

/-- Soundness plus completeness is exactness for the complex squared spectrum. -/
theorem complexSquaredExact_of_sound_complete
    {Spectrum : Type u} {energy : Spectrum -> ℂ}
    (hsound : ComplexSquaredSoundness energy)
    (hcomplete : ComplexSquaredCompleteness energy) :
    ComplexSquaredExact energy := by
  intro w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hcomplete z hz
  · rintro ⟨γ, rfl⟩
    rcases hsound γ with ⟨z, hz, hγ⟩
    exact ⟨z, hz, hγ⟩

/--
An abstract Meyer/Fork-A squared determinant carrier.

The rows `meyerScalingOperator`, `rieszBasisAtZeros`, `traceClassInverse`, and
`lidskiiDeterminantIdentity` name the source-native squared determinant
package.  The row `squaredZeroDictionary` is the resulting complex zero
dictionary.  None of these rows force RH.

The separate row `nonnegativeRealSquaredSpectrum` is the metric/polarization
upgrade: it supplies real energies and identifies the complex squared spectrum
with those nonnegative real energies.
-/
structure Carrier where
  Spectrum : Type u
  complexEnergy : Spectrum -> ℂ
  realEnergy : Spectrum -> ℝ
  meyerScalingOperator : Prop
  rieszBasisAtZeros : Prop
  traceClassInverse : Prop
  hilbertSchmidtInverse : Prop
  lidskiiDeterminantIdentity : Prop
  carlemanDet2Identity : Prop
  genusGaugeFixed : Prop
  squaredZeroDictionary : Prop
  nonnegativeRealSquaredSpectrum : Prop
  fakeFamilyRejection : Prop
  traceClass_of_rieszBasis :
    rieszBasisAtZeros -> traceClassInverse
  determinantIdentity_of_traceClass :
    traceClassInverse -> lidskiiDeterminantIdentity
  det2Identity_of_hilbertSchmidt :
    hilbertSchmidtInverse -> carlemanDet2Identity
  complexSound_of_dictionary :
    squaredZeroDictionary -> ComplexSquaredSoundness complexEnergy
  complexComplete_of_dictionary :
    squaredZeroDictionary -> ComplexSquaredCompleteness complexEnergy
  nonnegative_of_positiveRow :
    nonnegativeRealSquaredSpectrum -> NonnegativeSquaredSupport realEnergy
  complexEnergy_eq_real_of_positiveRow :
    nonnegativeRealSquaredSpectrum ->
      ∀ γ : Spectrum, complexEnergy γ = (realEnergy γ : ℂ)

namespace Carrier

/-- Meyer/Riesz rows imply the determinant-identity bookkeeping row. -/
theorem determinantIdentity_of_rieszBasis
    (C : Carrier.{u}) (hrb : C.rieszBasisAtZeros) :
    C.lidskiiDeterminantIdentity :=
  C.determinantIdentity_of_traceClass (C.traceClass_of_rieszBasis hrb)

/--
The RH-agnostic determinant-class rows.

Fork A can use either the ordinary trace-class/Lidskii determinant, or the
Hilbert--Schmidt/Carleman `det_2` determinant with the explicit genus-gauge
normalization fixed.
-/
def DeterminantClassRows (C : Carrier.{u}) : Prop :=
  (C.traceClassInverse ∧ C.lidskiiDeterminantIdentity) ∨
    (C.hilbertSchmidtInverse ∧ C.carlemanDet2Identity ∧ C.genusGaugeFixed)

/-- Riesz-basis control is a sufficient route to the trace-class determinant rows. -/
theorem determinantClassRows_of_rieszBasis
    (C : Carrier.{u}) (hrb : C.rieszBasisAtZeros) :
    C.DeterminantClassRows :=
  Or.inl ⟨C.traceClass_of_rieszBasis hrb, C.determinantIdentity_of_rieszBasis hrb⟩

/-- Hilbert--Schmidt control plus fixed genus gauge gives the det2 branch. -/
theorem determinantClassRows_of_hilbertSchmidt
    (C : Carrier.{u}) (hhs : C.hilbertSchmidtInverse)
    (hgauge : C.genusGaugeFixed) :
    C.DeterminantClassRows :=
  Or.inr ⟨hhs, C.det2Identity_of_hilbertSchmidt hhs, hgauge⟩

/-- The RH-agnostic Fork-A complex determinant rows. -/
def ComplexRows (C : Carrier.{u}) : Prop :=
  C.meyerScalingOperator ∧ C.DeterminantClassRows ∧ C.squaredZeroDictionary

/-- The positive squared-spectrum row needed for an RH handoff. -/
def PositiveRows (C : Carrier.{u}) : Prop :=
  C.nonnegativeRealSquaredSpectrum

/-- Full rows for a squared determinant RH handoff. -/
def FaithfulRows (C : Carrier.{u}) : Prop :=
  C.ComplexRows ∧ C.PositiveRows ∧ C.fakeFamilyRejection

/-- Complex rows alone supply only complex squared completeness. -/
theorem complexSquaredCompleteness_of_complexRows
    (C : Carrier.{u}) (h : C.ComplexRows) :
    ComplexSquaredCompleteness C.complexEnergy :=
  C.complexComplete_of_dictionary h.2.2

/-- Full rows supply exact nonnegative squared support. -/
theorem regularXiNonnegativeSquaredSupport_of_faithfulRows
    (C : Carrier.{u}) (h : C.FaithfulRows) :
    RegularXiNonnegativeSquaredSupport C.realEnergy := by
  refine ⟨C.nonnegative_of_positiveRow h.2.1, ?_⟩
  intro z hz
  rcases C.complexComplete_of_dictionary h.1.2.2 z hz with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  rw [← C.complexEnergy_eq_real_of_positiveRow h.2.1 γ]
  exact hγ

/-- Full rows prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u}) (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeSquaredSupport
    (C.regularXiNonnegativeSquaredSupport_of_faithfulRows h)

/-- A non-real regular zero blocks the positive row of any exact complex carrier. -/
theorem not_positiveRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0)
    (hdict : C.squaredZeroDictionary) :
    ¬ C.PositiveRows := by
  intro hpos
  have hsupport :
      RegularXiNonnegativeSquaredSupport C.realEnergy := by
    refine ⟨C.nonnegative_of_positiveRow hpos, ?_⟩
    intro y hy
    rcases C.complexComplete_of_dictionary hdict y hy with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [← C.complexEnergy_eq_real_of_positiveRow hpos γ]
    exact hγ
  exact hzim
    (regular_xi_zeros_real_of_nonnegativeSquaredSupport hsupport z hz)

/-- A non-real regular zero blocks the full Fork-A positive handoff. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows := by
  intro hrows
  exact C.not_positiveRows_of_nonrealRegularXiZero hz hzim hrows.1.2.2 hrows.2.1

end Carrier

/--
The canonical complex squared carrier: take the spectrum to be the regular
`Xi` zeros and the complex squared energy to be `z^2`.

This models the RH-agnostic determinant dictionary.  Its positive row is
precisely the assertion that all regular zeros are real.
-/
noncomputable def canonicalComplexSquaredCarrier : Carrier.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXiRegularZero z}
  complexEnergy := fun γ => γ.1 ^ 2
  realEnergy := fun γ => γ.1.re ^ 2
  meyerScalingOperator := True
  rieszBasisAtZeros := True
  traceClassInverse := True
  hilbertSchmidtInverse := True
  lidskiiDeterminantIdentity := True
  carlemanDet2Identity := True
  genusGaugeFixed := True
  squaredZeroDictionary := True
  nonnegativeRealSquaredSpectrum :=
    ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z}, γ.1.im = 0
  fakeFamilyRejection := True
  traceClass_of_rieszBasis := by
    intro _h
    trivial
  determinantIdentity_of_traceClass := by
    intro _h
    trivial
  det2Identity_of_hilbertSchmidt := by
    intro _h
    trivial
  complexSound_of_dictionary := by
    intro _h γ
    exact ⟨γ.1, γ.2, rfl⟩
  complexComplete_of_dictionary := by
    intro _h z hz
    exact ⟨⟨z, hz⟩, rfl⟩
  nonnegative_of_positiveRow := by
    intro _h γ
    exact sq_nonneg γ.1.re
  complexEnergy_eq_real_of_positiveRow := by
    intro hline γ
    have him : γ.1.im = 0 := hline γ
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, him]
    · simp [pow_two, Complex.mul_im, him]

/-- The canonical complex squared carrier has Fork-A complex rows unconditionally. -/
theorem canonicalComplexSquaredCarrier_complexRows :
    canonicalComplexSquaredCarrier.ComplexRows :=
  ⟨trivial, Or.inl ⟨trivial, trivial⟩, trivial⟩

/--
The positive row of the canonical complex squared carrier is exactly
mathlib's `RiemannHypothesis`.
-/
theorem canonicalComplexSquaredCarrier_positiveRows_iff_riemannHypothesis :
    canonicalComplexSquaredCarrier.PositiveRows ↔ RiemannHypothesis := by
  constructor
  · intro hpos
    exact (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
      (by
        intro z hz
        change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
          γ.1.im = 0 at hpos
        exact hpos ⟨z, hz⟩)
  · intro hRH
    change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
      γ.1.im = 0
    intro γ
    exact (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      hRH γ.1 γ.2

/-- A non-real regular zero makes the canonical complex squared carrier nonpositive. -/
theorem not_canonicalComplexSquaredCarrier_positiveRows_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ canonicalComplexSquaredCarrier.PositiveRows := by
  intro hpos
  change ∀ γ : {z : ℂ // RHReduction.riemannXiRegularZero z},
    γ.1.im = 0 at hpos
  exact hzim (hpos ⟨z, hz⟩)

/--
If RH is false via a non-real regular zero, Fork-A complex rows can still hold
while the positive squared-spectrum row fails.
-/
theorem complexRows_do_not_supply_positiveRows_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ∃ C : Carrier.{0}, C.ComplexRows ∧ ¬ C.PositiveRows :=
  ⟨canonicalComplexSquaredCarrier, canonicalComplexSquaredCarrier_complexRows,
    not_canonicalComplexSquaredCarrier_positiveRows_of_nonrealRegularXiZero
      hz hzim⟩

/-- A dummy source/Riesz carrier without a squared zero dictionary. -/
def dummyMeyerRowsCarrier : Carrier.{0} where
  Spectrum := PUnit
  complexEnergy := fun _ => Complex.I
  realEnergy := fun _ => 0
  meyerScalingOperator := True
  rieszBasisAtZeros := True
  traceClassInverse := True
  hilbertSchmidtInverse := True
  lidskiiDeterminantIdentity := True
  carlemanDet2Identity := True
  genusGaugeFixed := True
  squaredZeroDictionary := False
  nonnegativeRealSquaredSpectrum := False
  fakeFamilyRejection := True
  traceClass_of_rieszBasis := by
    intro _h
    trivial
  determinantIdentity_of_traceClass := by
    intro _h
    trivial
  det2Identity_of_hilbertSchmidt := by
    intro _h
    trivial
  complexSound_of_dictionary := by
    intro hdict
    cases hdict
  complexComplete_of_dictionary := by
    intro hdict
    cases hdict
  nonnegative_of_positiveRow := by
    intro hpos
    cases hpos
  complexEnergy_eq_real_of_positiveRow := by
    intro hpos
    cases hpos

/-- Meyer/Riesz-looking source rows alone do not supply the complex zero dictionary. -/
theorem meyerRieszRows_do_not_supply_complexRows :
    ∃ C : Carrier.{0},
      (C.meyerScalingOperator ∧ C.rieszBasisAtZeros) ∧ ¬ C.ComplexRows :=
  ⟨dummyMeyerRowsCarrier, ⟨trivial, trivial⟩, by
    intro hrows
    exact hrows.2.2⟩

/-- Existence of a faithful positive Fork-A squared carrier. -/
def HasFaithfulMeyerForkACarrier : Prop :=
  ∃ C : Carrier.{u}, C.FaithfulRows

/-- A faithful positive Fork-A squared carrier proves RH. -/
theorem riemannHypothesis_of_hasFaithfulMeyerForkACarrier
    (hC : HasFaithfulMeyerForkACarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_faithfulRows hrows

/-- RH supplies the canonical faithful carrier, tautologically. -/
theorem hasFaithfulMeyerForkACarrier_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    HasFaithfulMeyerForkACarrier.{0} := by
  refine ⟨canonicalComplexSquaredCarrier, ?_⟩
  exact ⟨canonicalComplexSquaredCarrier_complexRows,
    (canonicalComplexSquaredCarrier_positiveRows_iff_riemannHypothesis).2 hRH,
    trivial⟩

/--
At universe zero, the positive Fork-A squared interface has exactly RH strength.
The reverse direction is the circular zero-set carrier.
-/
theorem hasFaithfulMeyerForkACarrier_iff_riemannHypothesis :
    HasFaithfulMeyerForkACarrier.{0} ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_hasFaithfulMeyerForkACarrier
  · exact hasFaithfulMeyerForkACarrier_of_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful positive Fork-A carrier. -/
theorem not_hasFaithfulMeyerForkACarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulMeyerForkACarrier.{u} := by
  intro hC
  exact hzim
    ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      (riemannHypothesis_of_hasFaithfulMeyerForkACarrier hC) z hz)

end MeyerForkASquaredDeterminant
end JensenLadder
