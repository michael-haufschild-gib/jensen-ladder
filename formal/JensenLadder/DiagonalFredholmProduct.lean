import JensenLadder.SquaredVariablePullback
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic

/-!
# Diagonal Fredholm product surrogate

This module formalizes the tractable diagonal trace-class part of the ordinary
squared Fredholm target:

```text
  det(I - w A) = product_n (1 - w * lambda_n),
  sum_n ||lambda_n|| < infinity.
```

For a summable diagonal spectrum, the product converges locally uniformly on
the whole complex plane.  For a nonnegative real diagonal spectrum, the
nonzero eigenvalues define nonnegative squared energies `1 / lambda_n`; exact
faithfulness of those energies for regular `Xi` zeros feeds the existing
`SquaredVariablePullback` RH consumer.

This is not a full trace-class/Fredholm determinant theory, not a Schatten
ideal formalization, not a moment-problem theorem, and not a construction of
the zeta carrier.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace DiagonalFredholmProduct

open Filter Topology

/-- The ordinary diagonal Fredholm factor `1 - w * lambda`. -/
noncomputable def factor (lambda w : ℂ) : ℂ :=
  1 - w * lambda

/-- A nonzero diagonal Fredholm factor vanishes at `w = lambda⁻¹`. -/
theorem factor_eq_zero_iff {lambda w : ℂ} (hlambda : lambda ≠ 0) :
    factor lambda w = 0 ↔ w = lambda⁻¹ := by
  constructor
  · intro h
    have hmul : w * lambda = 1 := by
      exact (sub_eq_zero.mp h).symm
    calc
      w = w * 1 := by ring
      _ = w * (lambda * lambda⁻¹) := by rw [mul_inv_cancel₀ hlambda]
      _ = (w * lambda) * lambda⁻¹ := by ring
      _ = 1 * lambda⁻¹ := by rw [hmul]
      _ = lambda⁻¹ := by ring
  · intro hw
    subst hw
    simp [factor, inv_mul_cancel₀ hlambda]

/-- Off its inverse eigenvalue, a nonzero factor is nonzero. -/
theorem factor_ne_zero {lambda w : ℂ} (hlambda : lambda ≠ 0)
    (hw : w ≠ lambda⁻¹) :
    factor lambda w ≠ 0 := by
  rw [Ne, factor_eq_zero_iff hlambda]
  exact hw

/--
For a diagonal trace-class sequence `sum_n ||lambda_n|| < infinity`, the
ordinary Fredholm product factors converge locally uniformly on `ℂ`.
-/
theorem hasProdLocallyUniformlyOn_factors
    {lambda : ℕ → ℂ} (hsum : Summable (fun n => ‖lambda n‖)) :
    HasProdLocallyUniformlyOn
      (fun n w => factor (lambda n) w)
      (fun w => ∏' n, factor (lambda n) w) Set.univ := by
  have key : HasProdLocallyUniformlyOn
      (fun n w => 1 + (-(w * lambda n)))
      (fun w => ∏' n, (1 + (-(w * lambda n)))) Set.univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _hKsub hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set Rp : ℝ := max R 0 with hRp
    have hKRnorm : ∀ w ∈ K, ‖w‖ ≤ Rp := by
      intro w hw
      have hwc := hKR hw
      rw [Metric.mem_closedBall, dist_zero_right] at hwc
      exact hwc.trans (le_max_left _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      (u := fun n => Rp * ‖lambda n‖) (hsum.mul_left Rp) ?_ ?_
    · exact Filter.Eventually.of_forall fun n w hw => by
        calc
          ‖-(w * lambda n)‖ = ‖w‖ * ‖lambda n‖ := by
            rw [norm_neg, norm_mul]
          _ ≤ Rp * ‖lambda n‖ := by
            gcongr
            exact hKRnorm w hw
    · intro n
      exact Continuous.continuousOn (by fun_prop)
  have hfactor :
      (fun n w => 1 + (-(w * lambda n))) =
        fun n w => factor (lambda n) w := by
    funext n w
    simp [factor]
    ring
  have hprod :
      (fun w => ∏' n, (1 + (-(w * lambda n)))) =
        fun w => ∏' n, factor (lambda n) w := by
    funext w
    congr 1
  rw [hfactor, hprod] at key
  exact key

/-- A positive diagonal trace-class spectrum in the ordinary Fredholm target. -/
structure PositiveDiagonalTraceClassSpectrum where
  eigenvalue : ℕ → ℝ
  nonnegative : ∀ n : ℕ, 0 ≤ eigenvalue n
  traceClass : Summable (fun n : ℕ => ‖eigenvalue n‖)

namespace PositiveDiagonalTraceClassSpectrum

/-- Complex-valued eigenvalues for the analytic product. -/
noncomputable def eigenvalueComplex
    (S : PositiveDiagonalTraceClassSpectrum) (n : ℕ) : ℂ :=
  (S.eigenvalue n : ℂ)

/-- The ordinary diagonal Fredholm determinant product. -/
noncomputable def determinant
    (S : PositiveDiagonalTraceClassSpectrum) (w : ℂ) : ℂ :=
  ∏' n : ℕ, factor (S.eigenvalueComplex n) w

/-- The diagonal product converges locally uniformly on `ℂ`. -/
theorem determinant_hasProdLocallyUniformlyOn
    (S : PositiveDiagonalTraceClassSpectrum) :
    HasProdLocallyUniformlyOn
      (fun n w => factor (S.eigenvalueComplex n) w)
      S.determinant Set.univ := by
  have hsumC : Summable (fun n => ‖S.eigenvalueComplex n‖) := by
    simpa [eigenvalueComplex] using S.traceClass
  simpa [determinant] using hasProdLocallyUniformlyOn_factors
    (lambda := S.eigenvalueComplex) hsumC

/-- Nonzero diagonal indices, i.e. the eigenvalues that can create zeros. -/
def NonzeroIndex (S : PositiveDiagonalTraceClassSpectrum) : Type :=
  {n : ℕ // S.eigenvalue n ≠ 0}

/-- Squared energies corresponding to nonzero diagonal eigenvalues. -/
noncomputable def squaredEnergy
    (S : PositiveDiagonalTraceClassSpectrum) (n : S.NonzeroIndex) : ℝ :=
  (S.eigenvalue n.1)⁻¹

/-- Positivity of the squared energies follows from positivity of the diagonal spectrum. -/
theorem squaredEnergy_nonnegative
    (S : PositiveDiagonalTraceClassSpectrum) :
    SquaredVariablePullback.NonnegativeSquaredSupport S.squaredEnergy := by
  intro n
  exact inv_nonneg.mpr (S.nonnegative n.1)

/-- Nonzero positive diagonal eigenvalues give strictly positive squared energies. -/
theorem squaredEnergy_positive
    (S : PositiveDiagonalTraceClassSpectrum) (n : S.NonzeroIndex) :
    0 < S.squaredEnergy n := by
  have hpos : 0 < S.eigenvalue n.1 :=
    lt_of_le_of_ne (S.nonnegative n.1) n.2.symm
  exact inv_pos.mpr hpos

/-- A nonzero real diagonal Fredholm factor vanishes exactly at its squared energy. -/
theorem factor_eigenvalue_eq_zero_iff
    (S : PositiveDiagonalTraceClassSpectrum) (n : S.NonzeroIndex) {w : ℂ} :
    factor (S.eigenvalueComplex n.1) w = 0 ↔
      w = (S.squaredEnergy n : ℂ) := by
  have hlambda : S.eigenvalueComplex n.1 ≠ 0 := by
    change (S.eigenvalue n.1 : ℂ) ≠ 0
    exact_mod_cast n.2
  simpa [squaredEnergy, eigenvalueComplex, Complex.ofReal_inv] using
    (factor_eq_zero_iff (lambda := S.eigenvalueComplex n.1) (w := w) hlambda)

/--
Exact regular `Xi` faithfulness for the diagonal Fredholm spectrum: every
regular zero pulls back from an inverse nonzero eigenvalue.
-/
def RegularXiDiagonalFredholmCompleteness
    (S : PositiveDiagonalTraceClassSpectrum) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z →
    ∃ n : S.NonzeroIndex, z ^ 2 = (S.squaredEnergy n : ℂ)

/-- Exact diagonal Fredholm completeness supplies nonnegative squared support. -/
theorem regularXiNonnegativeSquaredSupport_of_completeness
    (S : PositiveDiagonalTraceClassSpectrum)
    (hcomplete : S.RegularXiDiagonalFredholmCompleteness) :
    SquaredVariablePullback.RegularXiNonnegativeSquaredSupport S.squaredEnergy :=
  ⟨S.squaredEnergy_nonnegative, hcomplete⟩

/--
A non-circular positive diagonal trace-class Fredholm product with exact
regular-zero completeness proves mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_completeness
    (S : PositiveDiagonalTraceClassSpectrum)
    (hcomplete : S.RegularXiDiagonalFredholmCompleteness) :
    RiemannHypothesis :=
  SquaredVariablePullback.riemannHypothesis_of_nonnegativeSquaredSupport
    (S.regularXiNonnegativeSquaredSupport_of_completeness hcomplete)

/-- A nonreal regular `Xi` zero blocks exact diagonal Fredholm completeness. -/
theorem not_completeness_of_nonrealRegularXiZero
    (S : PositiveDiagonalTraceClassSpectrum) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ S.RegularXiDiagonalFredholmCompleteness := by
  intro hcomplete
  have hsupport :=
    S.regularXiNonnegativeSquaredSupport_of_completeness hcomplete
  exact SquaredVariablePullback.not_faithful_of_nonrealRegularXiZero
    hsupport.1 hz hzim hsupport

end PositiveDiagonalTraceClassSpectrum

end DiagonalFredholmProduct
end JensenLadder
