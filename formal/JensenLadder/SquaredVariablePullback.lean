import JensenLadder.SpectralRealization
import Mathlib.Tactic

/-!
# Squared-variable pullback boundary

This module records the consumer for the `w = z^2` determinant target.

For the older signed squared-spectrum interface, a real value `-z^2` still needs
a central-axis side condition.  For the `det(D^2 - w)` target the spectral value
is instead `z^2`, and a positive operator supplies `z^2 = E` with `0 <= E`.
That has no central-axis ambiguity: if `z^2` is a nonnegative real number, then
`z` is real.

This is the formal pullback row behind the squared-variable carrier target.  It
does not construct `D`, prove determinant convergence, prove no spectral
pollution, prove the order-`1/2` Hadamard product theorem, or prove RH.

Evidence class: formal/certificate artifact; squared-variable consumer.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredVariablePullback

open SpectralRealization
open Filter Topology

universe u

/--
If `z^2` is a nonnegative real number, then `z` lies on the real axis.

This is the elementary algebraic advantage of the `w = z^2` target over the
signed `-z^2` interface.
-/
theorem im_eq_zero_of_sq_eq_nonneg_real {z : ℂ} {E : ℝ}
    (hE : 0 <= E) (hz : z ^ 2 = (E : ℂ)) :
    z.im = 0 := by
  have him : (z ^ 2).im = 0 := by
    rw [hz]
    simp
  simp [pow_two] at him
  have hprod : z.re * z.im = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hzre | hzim
  · have hreal : (z ^ 2).re = E := by
      rw [hz]
      simp
    simp [pow_two] at hreal
    have hEeq : E = -(z.im ^ 2) := by
      nlinarith [hzre]
    have hnonpos : E <= 0 := by
      nlinarith [sq_nonneg z.im]
    have hEzero : E = 0 := le_antisymm hnonpos hE
    have hyzero : z.im ^ 2 = 0 := by
      nlinarith [hEeq, hEzero]
    exact sq_eq_zero_iff.mp hyzero
  · exact hzim

/--
If `z^2` is a limit of nonnegative real squared spectral values, then `z` lies
on the real axis.

This is the approximation form needed by Hurwitz/determinant limits: finite
zeros need not hit `z^2` exactly, but if they converge to it from the closed
nonnegative real ray, the same pullback conclusion holds.
-/
theorem im_eq_zero_of_sq_tendsto_nonneg_reals {z : ℂ} {energy : ℕ → ℝ}
    (hnonneg : ∀ n : ℕ, 0 <= energy n)
    (htend : Tendsto (fun n : ℕ => (energy n : ℂ)) atTop (𝓝 (z ^ 2))) :
    z.im = 0 := by
  have hre_tend :
      Tendsto (fun n : ℕ => ((energy n : ℂ).re)) atTop (𝓝 ((z ^ 2).re)) :=
    (Complex.continuous_re.tendsto (z ^ 2)).comp htend
  have him_tend :
      Tendsto (fun n : ℕ => ((energy n : ℂ).im)) atTop (𝓝 ((z ^ 2).im)) :=
    (Complex.continuous_im.tendsto (z ^ 2)).comp htend
  have hre_nonneg : 0 <= (z ^ 2).re := by
    have hre_tend' : Tendsto energy atTop (𝓝 ((z ^ 2).re)) := by
      simpa using hre_tend
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hre_tend' hnonneg
  have him_zero : (z ^ 2).im = 0 := by
    have hzero_tend :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ((z ^ 2).im)) := by
      simpa using him_tend
    exact tendsto_nhds_unique hzero_tend tendsto_const_nhds
  have hprod : z.re * z.im = 0 := by
    simp [pow_two] at him_zero
    nlinarith
  rcases mul_eq_zero.mp hprod with hzre | hzim
  · have hnonpos : (z ^ 2).re <= 0 := by
      simp [pow_two, hzre]
      nlinarith [sq_nonneg z.im]
    have hre_zero : (z ^ 2).re = 0 := le_antisymm hnonpos hre_nonneg
    have hyzero : z.im ^ 2 = 0 := by
      simp [pow_two, hzre] at hre_zero
      nlinarith
    exact sq_eq_zero_iff.mp hyzero
  · exact hzim

/-- Nonnegativity of the squared spectral support supplied by a positive
operator such as `D^2`. -/
def NonnegativeSquaredSupport {Spectrum : Type u} (energy : Spectrum → ℝ) : Prop :=
  ∀ γ : Spectrum, 0 <= energy γ

/--
Exact faithfulness of nonnegative squared support for the regular `Xi` zeros.

The second row is the load-bearing dictionary: every regular `Xi` zero must
pull back from some nonnegative squared spectral value.
-/
def RegularXiNonnegativeSquaredSupport
    {Spectrum : Type u} (energy : Spectrum → ℝ) : Prop :=
  NonnegativeSquaredSupport energy ∧
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z →
      ∃ γ : Spectrum, z ^ 2 = (energy γ : ℂ)

/--
Approximate nonnegative squared support for regular `Xi` zeros.

For each regular zero `z`, `energy z n` is a nonnegative finite squared spectral
value whose complex embedding tends to `z^2`.  This is the direct consumer form
for a squared determinant/Hurwitz argument, before extracting an exact limiting
spectral point.
-/
def RegularXiNonnegativeSquaredApproximation
    (energy : ℂ → ℕ → ℝ) : Prop :=
  (∀ z : ℂ, ∀ n : ℕ, 0 <= energy z n) ∧
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z →
      Tendsto (fun n : ℕ => (energy z n : ℂ)) atTop (𝓝 (z ^ 2))

/-- A regular `Xi` zero missed by the nonnegative squared support. -/
def MissingRegularSquaredSupport
    {Spectrum : Type u} (energy : Spectrum → ℝ) : Prop :=
  ∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧
    ∀ γ : Spectrum, z ^ 2 ≠ (energy γ : ℂ)

/-- Exact squared-support faithfulness rules out missed regular `Xi` zeros. -/
theorem no_missingRegularSquaredSupport_of_faithful
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hfaithful : RegularXiNonnegativeSquaredSupport energy) :
    ¬ MissingRegularSquaredSupport energy := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases hfaithful.2 z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missed regular `Xi` zero falsifies exact squared-support faithfulness. -/
theorem not_faithful_of_missingRegularSquaredSupport
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hmiss : MissingRegularSquaredSupport energy) :
    ¬ RegularXiNonnegativeSquaredSupport energy := by
  intro hfaithful
  exact no_missingRegularSquaredSupport_of_faithful hfaithful hmiss

/--
Nonnegative squared-support faithfulness forces every regular `Xi` zero onto the
real axis in the `Xi` coordinate.
-/
theorem regular_xi_zeros_real_of_nonnegativeSquaredSupport
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hfaithful : RegularXiNonnegativeSquaredSupport energy) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  rcases hfaithful.2 z hz with ⟨γ, hγ⟩
  exact im_eq_zero_of_sq_eq_nonneg_real (hfaithful.1 γ) hγ

/--
Approximate nonnegative squared-support faithfulness is already enough to force
every regular `Xi` zero onto the real axis.
-/
theorem regular_xi_zeros_real_of_nonnegativeSquaredApproximation
    {energy : ℂ → ℕ → ℝ}
    (happrox : RegularXiNonnegativeSquaredApproximation energy) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  exact im_eq_zero_of_sq_tendsto_nonneg_reals
    (fun n => happrox.1 z n) (happrox.2 z hz)

/--
A non-circular proof of nonnegative squared-support faithfulness would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_nonnegativeSquaredSupport
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hfaithful : RegularXiNonnegativeSquaredSupport energy) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (regular_xi_zeros_real_of_nonnegativeSquaredSupport hfaithful)

/--
A non-circular proof of approximate nonnegative squared support would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_nonnegativeSquaredApproximation
    {energy : ℂ → ℕ → ℝ}
    (happrox : RegularXiNonnegativeSquaredApproximation energy) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (regular_xi_zeros_real_of_nonnegativeSquaredApproximation happrox)

/-- A nonreal regular `Xi` zero is missed by every nonnegative squared support. -/
theorem missingRegularSquaredSupport_of_nonrealRegularXiZero
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hnonneg : NonnegativeSquaredSupport energy) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    MissingRegularSquaredSupport energy := by
  refine ⟨z, hz, ?_⟩
  intro γ hγ
  exact hzim (im_eq_zero_of_sq_eq_nonneg_real (hnonneg γ) hγ)

/-- A nonreal regular `Xi` zero blocks exact nonnegative squared support. -/
theorem not_faithful_of_nonrealRegularXiZero
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hnonneg : NonnegativeSquaredSupport energy) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ RegularXiNonnegativeSquaredSupport energy :=
  not_faithful_of_missingRegularSquaredSupport
    (missingRegularSquaredSupport_of_nonrealRegularXiZero hnonneg hz hzim)

/-- A nonreal regular `Xi` zero blocks approximate nonnegative squared support. -/
theorem not_approximation_of_nonrealRegularXiZero
    {energy : ℂ → ℕ → ℝ} {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ RegularXiNonnegativeSquaredApproximation energy := by
  intro happrox
  exact hzim
    (regular_xi_zeros_real_of_nonnegativeSquaredApproximation happrox z hz)

/-- Packaged endpoint for a positive squared-spectrum carrier. -/
structure RiemannXiNonnegativeSquaredSupport where
  Spectrum : Type u
  energy : Spectrum → ℝ
  faithful : RegularXiNonnegativeSquaredSupport energy

/-- Packaged endpoint for an approximating positive squared-spectrum carrier. -/
structure RiemannXiNonnegativeSquaredApproximation where
  energy : ℂ → ℕ → ℝ
  faithful : RegularXiNonnegativeSquaredApproximation energy

namespace RiemannXiNonnegativeSquaredSupport

/-- The packaged endpoint forces regular `Xi` zeros onto the real axis. -/
theorem regular_xi_zeros_real
    (S : RiemannXiNonnegativeSquaredSupport.{u}) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
  regular_xi_zeros_real_of_nonnegativeSquaredSupport S.faithful

/-- The packaged endpoint proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (S : RiemannXiNonnegativeSquaredSupport.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeSquaredSupport S.faithful

end RiemannXiNonnegativeSquaredSupport

namespace RiemannXiNonnegativeSquaredApproximation

/-- The packaged approximation endpoint forces regular `Xi` zeros onto the real axis. -/
theorem regular_xi_zeros_real
    (S : RiemannXiNonnegativeSquaredApproximation) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
  regular_xi_zeros_real_of_nonnegativeSquaredApproximation S.faithful

/-- The packaged approximation endpoint proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (S : RiemannXiNonnegativeSquaredApproximation) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeSquaredApproximation S.faithful

end RiemannXiNonnegativeSquaredApproximation

end SquaredVariablePullback
end JensenLadder
