import JensenLadder.CVSSpectralRoute

/-!
# Determinant Hurwitz route

This module specializes the abstract C-vS Hurwitz handoff to the determinant
route suggested by the CCM/Suzuki spectral-triple program.

The determinant route has a narrower shape than eigenvalue-branch tracking:

* each finite regularized determinant has only real zeros;
* the normalized determinants converge locally uniformly to `Xi`;
* Hurwitz/LP-closure transfers real-zero-ness to the regular `Xi` endpoint.

The analytic Hurwitz theorem and the local-uniform convergence estimate are not
proved here.  They are represented by the single load-bearing row
`locallyUniformToXi`, plus the transfer field that turns that row into reality of
regular `Xi` zeros.  This file only packages that row into the existing
`CVSSpectralRoute` interface.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

namespace JensenLadder
namespace DeterminantHurwitzRoute

open CVSSpectralRoute

universe u

/--
A finite-scale family of regularized determinants.

For the intended CCM/Suzuki application, each `determinant a` is the normalized
regularized characteristic determinant of a finite self-adjoint operator.  This
structure deliberately stores only the function family needed by the zero-set
handoff; self-adjointness and regularization conventions are external analytic
data.
-/
structure DeterminantApproximants where
  Scale : Type u
  determinant : Scale -> Complex -> Complex

namespace DeterminantApproximants

/-- Forget determinant vocabulary and view the family as finite approximants. -/
def toFiniteScaleApproximants (D : DeterminantApproximants.{u}) :
    FiniteScaleApproximants.{u} where
  Scale := D.Scale
  approximant := D.determinant

/-- Every zero of every finite determinant is real. -/
def AllZerosReal (D : DeterminantApproximants.{u}) : Prop :=
  forall a : D.Scale, forall z : Complex, D.determinant a z = 0 -> z.im = 0

/-- Determinant real-zero data supplies the generic finite-approximant row. -/
theorem allApproximantZerosReal_of_allZerosReal
    (D : DeterminantApproximants.{u})
    (hreal : D.AllZerosReal) :
    AllApproximantZerosReal D.toFiniteScaleApproximants := by
  intro a z hz
  exact hreal a z hz

/-- The generic finite-approximant real-zero row is the same determinant row. -/
theorem allZerosReal_of_allApproximantZerosReal
    (D : DeterminantApproximants.{u})
    (hreal : AllApproximantZerosReal D.toFiniteScaleApproximants) :
    D.AllZerosReal := by
  intro a z hz
  exact hreal a z hz

/--
The determinant-route Hurwitz row.

`locallyUniformToXi` is the analytic estimate: normalized determinants converge
to `RHReduction.riemannXi` locally uniformly on compact subsets, with the
normalization and nonzero-limit hypotheses included in the external theorem.
The transfer field is the Hurwitz/LP-closure consequence needed by the RH
handoff.
-/
structure HurwitzConvergence (D : DeterminantApproximants.{u}) where
  locallyUniformToXi : Prop
  regularXiZerosReal_of_realZeros_and_locallyUniform :
    D.AllZerosReal -> locallyUniformToXi ->
      forall z : Complex, RHReduction.riemannXiRegularZero z -> z.im = 0

namespace HurwitzConvergence

/-- Repackage determinant convergence as the existing C-vS Hurwitz row. -/
def toCVSHurwitzXiConvergence
    {D : DeterminantApproximants.{u}}
    (H : HurwitzConvergence D) :
    HurwitzXiConvergence D.toFiniteScaleApproximants where
  convergesToXi := H.locallyUniformToXi
  regularXiZerosReal_of_approximantsReal_and_convergence := by
    intro hreal hconv z hz
    exact H.regularXiZerosReal_of_realZeros_and_locallyUniform
      (D.allZerosReal_of_allApproximantZerosReal hreal) hconv z hz

end HurwitzConvergence

/--
Finite determinant real-zero data plus the determinant Hurwitz row proves
mathlib's `RiemannHypothesis`.

The hard input is `hconv`: the locally-uniform convergence theorem.
-/
theorem riemannHypothesis_of_allZerosReal_and_locallyUniform
    (D : DeterminantApproximants.{u})
    (H : D.HurwitzConvergence)
    (hreal : D.AllZerosReal)
    (hconv : H.locallyUniformToXi) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (H.regularXiZerosReal_of_realZeros_and_locallyUniform hreal hconv)

/--
A non-real regular `Xi` zero refutes the locally-uniform determinant convergence
row, assuming every finite determinant has only real zeros.
-/
theorem not_locallyUniformToXi_of_nonrealRegularXiZero_and_allZerosReal
    (D : DeterminantApproximants.{u})
    (H : D.HurwitzConvergence)
    (hreal : D.AllZerosReal)
    {z : Complex}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    Not H.locallyUniformToXi := by
  intro hconv
  exact hzim
    (H.regularXiZerosReal_of_realZeros_and_locallyUniform hreal hconv z hz)

/-- Packaged determinant-route RH certificate. -/
structure DeterminantHurwitzRHCertificate where
  approximants : DeterminantApproximants.{u}
  convergence : approximants.HurwitzConvergence
  allZerosReal : approximants.AllZerosReal
  locallyUniformToXi : convergence.locallyUniformToXi

namespace DeterminantHurwitzRHCertificate

/-- The packaged determinant row as the generic C-vS convergence interface. -/
def cvsConvergence
    (cert : DeterminantHurwitzRHCertificate.{u}) :
    HurwitzXiConvergence cert.approximants.toFiniteScaleApproximants :=
  cert.convergence.toCVSHurwitzXiConvergence

/-- A packaged determinant Hurwitz certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : DeterminantHurwitzRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.approximants.riemannHypothesis_of_allZerosReal_and_locallyUniform
    cert.convergence cert.allZerosReal cert.locallyUniformToXi

end DeterminantHurwitzRHCertificate

end DeterminantApproximants

end DeterminantHurwitzRoute
end JensenLadder
