import JensenLadder.SquaredVariablePullback

/-!
# Squared determinant approximation bridge

This module packages the determinant-specific row behind the squared-variable
target `det(D^2 - w)`.

The previous pullback module proves that a regular `Xi` zero is real if its
square lies in the closure of the nonnegative real squared-spectrum.  This file
connects that consumer to finite determinant data:

* every finite squared determinant zero lies on the nonnegative real ray;
* every regular `Xi` zero is shadowed by finite squared determinant zeros
  converging to `z^2`.

Those two rows are exactly the squared determinant/Hurwitz burden.  This module
does not construct the operator, prove determinant convergence, prove the
order-`1/2` product theorem, or prove RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantApproximation

open Filter Topology

universe u

/-- A finite-scale family of squared-variable determinants. -/
structure SquaredDeterminantApproximants where
  Scale : Type u
  determinant : Scale -> ℂ -> ℂ

namespace SquaredDeterminantApproximants

/-- Every zero of every finite squared determinant lies on the nonnegative real ray. -/
def AllZerosNonnegativeReal (D : SquaredDeterminantApproximants.{u}) : Prop :=
  ∀ a : D.Scale, ∀ w : ℂ, D.determinant a w = 0 →
    ∃ E : ℝ, 0 <= E ∧ w = (E : ℂ)

/--
Every regular `Xi` zero has finite squared-determinant zeros converging to
`z^2`.

This is the squared-variable analogue of a Hurwitz zero-detection row.
-/
def RegularXiSquaredZeroShadowing
    (D : SquaredDeterminantApproximants.{u}) (scale : ℕ -> D.Scale) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z →
    ∃ w : ℕ -> ℂ,
      (∀ n : ℕ, D.determinant (scale n) (w n) = 0) ∧
        Tendsto w atTop (𝓝 (z ^ 2))

/--
If finite determinant zeros lie on the nonnegative real ray and shadow every
regular `Xi` zero, then the abstract nonnegative squared approximation row is
available.
-/
theorem exists_nonnegativeSquaredApproximation_of_shadowing
    (D : SquaredDeterminantApproximants.{u}) (scale : ℕ -> D.Scale)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hshadow : D.RegularXiSquaredZeroShadowing scale) :
    ∃ energy : ℂ -> ℕ -> ℝ,
      SquaredVariablePullback.RegularXiNonnegativeSquaredApproximation energy := by
  classical
  choose w hwzero hwtend using hshadow
  let energy : ℂ -> ℕ -> ℝ := fun z n =>
    if hz : RHReduction.riemannXiRegularZero z then
      Classical.choose (hnonneg (scale n) (w z hz n) (hwzero z hz n))
    else 0
  refine ⟨energy, ?_, ?_⟩
  · intro z n
    by_cases hz : RHReduction.riemannXiRegularZero z
    · have hspec :=
        Classical.choose_spec (hnonneg (scale n) (w z hz n) (hwzero z hz n))
      simpa [energy, hz] using hspec.1
    · simp [energy, hz]
  · intro z hz
    have hseq : (fun n : ℕ => (energy z n : ℂ)) = w z hz := by
      funext n
      have hspec :=
        Classical.choose_spec (hnonneg (scale n) (w z hz n) (hwzero z hz n))
      simpa [energy, hz] using hspec.2.symm
    simpa [hseq] using hwtend z hz

/--
Finite nonnegative-real determinant zeros plus regular-zero shadowing force all
regular `Xi` zeros to be real.
-/
theorem regular_xi_zeros_real_of_shadowing
    (D : SquaredDeterminantApproximants.{u}) (scale : ℕ -> D.Scale)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hshadow : D.RegularXiSquaredZeroShadowing scale) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z -> z.im = 0 := by
  rcases exists_nonnegativeSquaredApproximation_of_shadowing D scale hnonneg hshadow with
    ⟨energy, happrox⟩
  exact SquaredVariablePullback.regular_xi_zeros_real_of_nonnegativeSquaredApproximation
    happrox

/--
The squared determinant approximation bridge proves mathlib's
`RiemannHypothesis` once its two determinant rows are supplied.
-/
theorem riemannHypothesis_of_shadowing
    (D : SquaredDeterminantApproximants.{u}) (scale : ℕ -> D.Scale)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hshadow : D.RegularXiSquaredZeroShadowing scale) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (D.regular_xi_zeros_real_of_shadowing scale hnonneg hshadow)

/--
A nonreal regular `Xi` zero refutes the shadowing row whenever all finite
squared determinant zeros are nonnegative real.
-/
theorem not_shadowing_of_nonrealRegularXiZero
    (D : SquaredDeterminantApproximants.{u}) (scale : ℕ -> D.Scale)
    (hnonneg : D.AllZerosNonnegativeReal) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ D.RegularXiSquaredZeroShadowing scale := by
  intro hshadow
  exact hzim (D.regular_xi_zeros_real_of_shadowing scale hnonneg hshadow z hz)

end SquaredDeterminantApproximants

/-- Packaged squared determinant approximation certificate. -/
structure SquaredDeterminantApproximationCertificate where
  approximants : SquaredDeterminantApproximants.{u}
  scale : ℕ -> approximants.Scale
  allZerosNonnegativeReal : approximants.AllZerosNonnegativeReal
  regularXiSquaredZeroShadowing :
    approximants.RegularXiSquaredZeroShadowing scale

namespace SquaredDeterminantApproximationCertificate

/-- A packaged squared determinant approximation certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : SquaredDeterminantApproximationCertificate.{u}) :
    RiemannHypothesis :=
  cert.approximants.riemannHypothesis_of_shadowing cert.scale
    cert.allZerosNonnegativeReal cert.regularXiSquaredZeroShadowing

end SquaredDeterminantApproximationCertificate

end SquaredDeterminantApproximation
end JensenLadder
