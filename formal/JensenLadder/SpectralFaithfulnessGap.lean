import JensenLadder.SpectralRealization

/-!
# Spectral faithfulness gap

Self-adjoint scaling/prolate candidates naturally provide real spectral values.
For the squared endpoint this is represented by a real-valued map
`energy : Spectrum -> R`.  Real spectrum alone is not the RH-bearing input:
the open part is exact faithfulness, namely that every regular `Xi` zero is
represented by some real energy value `-z^2`.

This file makes the complementary falsifier explicit.  If a regular `Xi` zero
is not represented by the candidate's squared spectrum, then the squared
faithfulness row fails.  This is the Lean-facing form of the "density/reality is
free; exact per-zero faithfulness is the gap" diagnosis.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace SpectralFaithfulnessGap

open SpectralRealization

universe u

/--
A regular `Xi` zero that is not represented by a squared real-spectrum
candidate.

For squared spectral candidates, a zero `z` must be represented by a real energy
`-z^2 = E`.  An unrepresented zero is therefore an exact witness that the
candidate has only partial or density-level agreement with the zero set.
-/
def UnrepresentedRegularXiZero {Spectrum : Type u} (energy : Spectrum -> ℝ) : Prop :=
  exists z : ℂ, RHReduction.riemannXiRegularZero z ∧
    forall γ : Spectrum, -z ^ 2 ≠ (energy γ : ℂ)

/-- An unrepresented regular zero falsifies squared spectral faithfulness. -/
theorem not_squaredFaithfulness_of_unrepresentedRegularXiZero
    {Spectrum : Type u} {energy : Spectrum -> ℝ}
    (hmiss : UnrepresentedRegularXiZero energy) :
    ¬ RegularXiSquaredFaithfulness energy := by
  intro hfaithful
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases hfaithful z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- Squared spectral faithfulness rules out unrepresented regular zeros. -/
theorem no_unrepresentedRegularXiZero_of_squaredFaithfulness
    {Spectrum : Type u} {energy : Spectrum -> ℝ}
    (hfaithful : RegularXiSquaredFaithfulness energy) :
    ¬ UnrepresentedRegularXiZero energy := by
  intro hmiss
  exact not_squaredFaithfulness_of_unrepresentedRegularXiZero hmiss hfaithful

/--
An off-axis, noncentral regular `Xi` zero cannot be represented by any real
squared spectrum.

This is the algebra behind the "real spectrum is free; faithfulness is the gap"
diagnosis.  If `z.re ≠ 0` and `z.im ≠ 0`, then `-z^2` is not real, so it cannot
equal a real energy value.
-/
theorem unrepresentedRegularXiZero_of_offAxisRegularXiZero
    {Spectrum : Type u} (energy : Spectrum -> ℝ) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzre : z.re ≠ 0)
    (hzim : z.im ≠ 0) :
    UnrepresentedRegularXiZero energy := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (im_eq_zero_of_neg_sq_eq_real hzre hγ)

/--
Any off-axis, noncentral regular `Xi` zero falsifies squared spectral
faithfulness for every real-energy candidate.
-/
theorem not_squaredFaithfulness_of_offAxisRegularXiZero
    {Spectrum : Type u} {energy : Spectrum -> ℝ} {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzre : z.re ≠ 0)
    (hzim : z.im ≠ 0) :
    ¬ RegularXiSquaredFaithfulness energy :=
  not_squaredFaithfulness_of_unrepresentedRegularXiZero
    (unrepresentedRegularXiZero_of_offAxisRegularXiZero energy hz hzre hzim)

/--
Minimal squared-spectrum candidate data.

The real-valued `energy` field is the part supplied by self-adjointness or a
manifestly real spectral construction.  No RH conclusion follows from this data
alone; it must be extended by `FaithfulSquaredSpectrumCandidate`.
-/
structure SquaredSpectrumCandidate where
  Spectrum : Type u
  energy : Spectrum -> ℝ

/-- Faithfulness predicate for a squared-spectrum candidate. -/
def SquaredSpectrumCandidate.Faithful (S : SquaredSpectrumCandidate.{u}) : Prop :=
  RegularXiSquaredFaithfulness S.energy

/-- Missing-zero predicate for a squared-spectrum candidate. -/
def SquaredSpectrumCandidate.UnrepresentedZero (S : SquaredSpectrumCandidate.{u}) : Prop :=
  UnrepresentedRegularXiZero S.energy

/-- A missing regular zero blocks faithfulness of a squared-spectrum candidate. -/
theorem SquaredSpectrumCandidate.not_faithful_of_unrepresentedZero
    (S : SquaredSpectrumCandidate.{u})
    (hmiss : S.UnrepresentedZero) :
    ¬ S.Faithful :=
  not_squaredFaithfulness_of_unrepresentedRegularXiZero hmiss

/--
A squared-spectrum candidate with the two actual RH-bearing rows:

* central-axis exclusion for the squared coordinate;
* faithful representation of every regular `Xi` zero.
-/
structure FaithfulSquaredSpectrumCandidate extends SquaredSpectrumCandidate.{u} where
  noncentral : NoCentralRegularXiZero
  faithful : toSquaredSpectrumCandidate.Faithful

/-- A faithful squared-spectrum candidate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_faithfulSquaredSpectrumCandidate
    (S : FaithfulSquaredSpectrumCandidate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_squaredFaithfulness S.noncentral S.faithful

end SpectralFaithfulnessGap
end JensenLadder
