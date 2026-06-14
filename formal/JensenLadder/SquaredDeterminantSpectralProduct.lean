import JensenLadder.SquaredDeterminantApproximation

/-!
# Finite squared spectral product support

This module proves the finite product row behind the nonnegative squared
determinant hypothesis.

For a finite spectral product

```text
  det_a(w) = ∏ i, (E_a(i) - w)
```

with every `E_a(i) >= 0`, every zero of `det_a` lies on the nonnegative real
ray.  This discharges the finite diagonal/spectral-product version of
`SquaredDeterminantApproximants.AllZerosNonnegativeReal`.

The module does not prove that a concrete operator has this product
representation, does not prove variable-zero shadowing, does not prove
determinant convergence, and does not prove RH.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantSpectralProduct

open scoped BigOperators

universe u

/-- A finite list of nonnegative squared energies, represented as an indexed
finite spectrum. -/
structure FiniteSquaredSpectrum where
  Index : Type u
  fintype : Fintype Index
  energy : Index -> ℝ
  nonnegative : ∀ i : Index, 0 <= energy i

namespace FiniteSquaredSpectrum

/-- The finite squared spectral determinant `∏ i, (E_i - w)`. -/
noncomputable def determinant (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : ℂ := by
  letI := S.fintype
  exact ∏ i : S.Index, ((S.energy i : ℂ) - w)

/-- Every zero of a finite squared spectral product is one of its nonnegative
real energies. -/
theorem exists_nonnegative_energy_of_determinant_eq_zero
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hw : S.determinant w = 0) :
    ∃ E : ℝ, 0 <= E ∧ w = (E : ℂ) := by
  classical
  letI := S.fintype
  unfold determinant at hw
  rw [Finset.prod_eq_zero_iff] at hw
  rcases hw with ⟨i, _hi, hzero⟩
  exact ⟨S.energy i, S.nonnegative i, (sub_eq_zero.mp hzero).symm⟩

end FiniteSquaredSpectrum

/-- A scale-indexed family of finite nonnegative squared spectra. -/
structure FiniteSquaredSpectrumFamily where
  Scale : Type u
  spectrum : Scale -> FiniteSquaredSpectrum.{u}

namespace FiniteSquaredSpectrumFamily

/-- The squared determinant approximants associated to the finite spectral
products. -/
noncomputable def approximants (F : FiniteSquaredSpectrumFamily.{u}) :
    SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u} where
  Scale := F.Scale
  determinant := fun a w => (F.spectrum a).determinant w

/-- Finite nonnegative squared spectral products have only nonnegative real
zeros. -/
theorem allZerosNonnegativeReal
    (F : FiniteSquaredSpectrumFamily.{u}) :
    F.approximants.AllZerosNonnegativeReal := by
  intro a w hw
  exact (F.spectrum a).exists_nonnegative_energy_of_determinant_eq_zero hw

/--
A finite spectral-product family proves RH once its squared determinant zeros
shadow every regular `Xi` zero.
-/
theorem riemannHypothesis_of_squaredZeroShadowing
    (F : FiniteSquaredSpectrumFamily.{u}) (scale : ℕ -> F.Scale)
    (hshadow : F.approximants.RegularXiSquaredZeroShadowing scale) :
    RiemannHypothesis :=
  F.approximants.riemannHypothesis_of_shadowing scale
    F.allZerosNonnegativeReal hshadow

/--
A nonreal regular `Xi` zero refutes squared zero-shadowing for any finite
nonnegative squared spectral product family.
-/
theorem not_squaredZeroShadowing_of_nonrealRegularXiZero
    (F : FiniteSquaredSpectrumFamily.{u}) (scale : ℕ -> F.Scale) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ F.approximants.RegularXiSquaredZeroShadowing scale :=
  F.approximants.not_shadowing_of_nonrealRegularXiZero scale
    F.allZerosNonnegativeReal hz hzim

end FiniteSquaredSpectrumFamily

/-- Packaged finite spectral-product squared determinant certificate. -/
structure FiniteSpectralProductCertificate where
  family : FiniteSquaredSpectrumFamily.{u}
  scale : ℕ -> family.Scale
  squaredZeroShadowing : family.approximants.RegularXiSquaredZeroShadowing scale

namespace FiniteSpectralProductCertificate

/-- A packaged finite spectral-product certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : FiniteSpectralProductCertificate.{u}) :
    RiemannHypothesis :=
  cert.family.riemannHypothesis_of_squaredZeroShadowing cert.scale
    cert.squaredZeroShadowing

end FiniteSpectralProductCertificate

end SquaredDeterminantSpectralProduct
end JensenLadder
