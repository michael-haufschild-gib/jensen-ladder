import JensenLadder.SquaredDeterminantSpectralProduct
import JensenLadder.SquaredDeterminantZeroTransfer

/-!
# Paired gauge spectral-product bridge

This module composes the two finite rows behind the squared determinant target:

* paired gauge cancellation transfers target zeros in `z` to determinant zeros
  in `w = z^2`;
* a finite product over nonnegative squared energies has zeros only on the
  nonnegative real ray.

The product representation remains an explicit field.  This module does not
prove that a concrete operator has such a representation, does not prove
variable-zero shadowing, does not prove determinant convergence, and does not
prove RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantPairedSpectralProduct

universe u

open SquaredDeterminantSpectralProduct
open SquaredDeterminantZeroTransfer

/--
A paired gauge family whose squared determinants are finite products over
nonnegative squared energies on the same scales.
-/
structure PairedSpectralProductFamily where
  gauge : PairedGaugeApproximants.{u}
  spectrum : gauge.Scale -> FiniteSquaredSpectrum.{u}
  squareDet_eq_product :
    ∀ a : gauge.Scale, ∀ w : ℂ,
      (gauge.model a).squareDet w = (spectrum a).determinant w

namespace PairedSpectralProductFamily

/-- The finite spectral-product family associated to the paired gauge family. -/
noncomputable def spectralFamily (F : PairedSpectralProductFamily.{u}) :
    FiniteSquaredSpectrumFamily.{u} where
  Scale := F.gauge.Scale
  spectrum := F.spectrum

/-- The associated squared determinant zeros lie on the nonnegative real ray. -/
theorem allZerosNonnegativeReal
    (F : PairedSpectralProductFamily.{u}) :
    F.gauge.squaredDeterminants.AllZerosNonnegativeReal := by
  intro a w hw
  have hprod : (F.spectrum a).determinant w = 0 := by
    rw [← F.squareDet_eq_product a w]
    exact hw
  exact (F.spectrum a).exists_nonnegative_energy_of_determinant_eq_zero hprod

/--
If target zeros shadow every regular `Xi` zero in the original variable, the
paired spectral-product bridge proves mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_variableZeroShadowing
    (F : PairedSpectralProductFamily.{u}) (scale : ℕ -> F.gauge.Scale)
    (hshadow : F.gauge.RegularXiVariableZeroShadowing scale) :
    RiemannHypothesis :=
  F.gauge.riemannHypothesis_of_variableZeroShadowing scale
    F.allZerosNonnegativeReal hshadow

/--
A nonreal regular `Xi` zero refutes variable-level shadowing through any paired
spectral-product bridge.
-/
theorem not_variableZeroShadowing_of_nonrealRegularXiZero
    (F : PairedSpectralProductFamily.{u}) (scale : ℕ -> F.gauge.Scale)
    {z : ℂ} (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ F.gauge.RegularXiVariableZeroShadowing scale :=
  F.gauge.not_variableZeroShadowing_of_nonrealRegularXiZero scale
    F.allZerosNonnegativeReal hz hzim

end PairedSpectralProductFamily

/-- Packaged paired spectral-product zero-shadowing certificate. -/
structure PairedSpectralProductCertificate where
  family : PairedSpectralProductFamily.{u}
  scale : ℕ -> family.gauge.Scale
  variableZeroShadowing : family.gauge.RegularXiVariableZeroShadowing scale

namespace PairedSpectralProductCertificate

/-- A packaged paired spectral-product certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : PairedSpectralProductCertificate.{u}) :
    RiemannHypothesis :=
  cert.family.riemannHypothesis_of_variableZeroShadowing cert.scale
    cert.variableZeroShadowing

end PairedSpectralProductCertificate

end SquaredDeterminantPairedSpectralProduct
end JensenLadder
