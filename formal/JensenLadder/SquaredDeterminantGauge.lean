import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Squared determinant gauge cancellation

This module records the finite algebra behind the squared-variable determinant
target.

If a determinant identity in the `z` variable carries a zero-free exponential
gauge `exp(a z)`, the paired product at `z` and `-z` cancels that gauge:

```text
  exp(a z) * exp(a (-z)) = 1.
```

Thus, for an even approximant `F`, a paired determinant product has the square
target

```text
  scalar * F(z)^2
```

without a residual `exp(a z)` factor.  This is only normalization algebra.  It
does not construct the operator, prove determinant convergence, prove spectral
faithfulness, prove the order-`1/2` Hadamard theorem, or prove RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantGauge

/-- The paired exponential gauge in the variables `z` and `-z` cancels exactly. -/
theorem exp_gauge_pair_cancel (a z : ℂ) :
    Complex.exp (a * z) * Complex.exp (a * (-z)) = 1 := by
  rw [← Complex.exp_add]
  have h : a * z + a * (-z) = 0 := by
    ring
  rw [h]
  simp

/--
If the finite determinant side is an exponential gauge times an even function,
then the paired `z`/`-z` product has no exponential gauge and equals the scalar
product times the square of the even function.
-/
theorem paired_gauge_product_eq_const_mul_sq
    (a c d : ℂ) (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z) (z : ℂ) :
    (c * Complex.exp (a * z) * F z) *
        (d * Complex.exp (a * (-z)) * F (-z)) =
      c * d * (F z) ^ 2 := by
  rw [heven z]
  have hcancel : Complex.exp (a * z) * Complex.exp (a * (-z)) = 1 :=
    exp_gauge_pair_cancel a z
  calc
    (c * Complex.exp (a * z) * F z) *
        (d * Complex.exp (a * (-z)) * F z)
        = c * d * (F z) ^ 2 *
            (Complex.exp (a * z) * Complex.exp (a * (-z))) := by
          ring
    _ = c * d * (F z) ^ 2 := by
      rw [hcancel]
      ring

/--
Abstract finite paired determinant model.

`detMinus` and `detPlus` are the two determinant factors at `z` and `-z`;
`squareDet` is the determinant object in the squared variable; `approximant` is
the even finite function being targeted after removing the gauge.  The field
`squareDet_eq_pair` is where a concrete determinant theory must prove
multiplicativity.  For regularized determinants this is a theorem row, not
bookkeeping.
-/
structure PairedGaugeModel where
  detMinus : ℂ → ℂ
  detPlus : ℂ → ℂ
  squareDet : ℂ → ℂ
  approximant : ℂ → ℂ
  gaugeSlope : ℂ
  leftConst : ℂ
  rightConst : ℂ
  approximant_even : ∀ z : ℂ, approximant (-z) = approximant z
  detMinus_eq :
    ∀ z : ℂ,
      detMinus z =
        leftConst * Complex.exp (gaugeSlope * z) * approximant z
  detPlus_eq :
    ∀ z : ℂ,
      detPlus z =
        rightConst * Complex.exp (gaugeSlope * (-z)) * approximant (-z)
  squareDet_eq_pair :
    ∀ z : ℂ, squareDet (z ^ 2) = detMinus z * detPlus z

namespace PairedGaugeModel

/--
In an abstract paired determinant model, the squared-variable determinant has
no residual exponential gauge.
-/
theorem squareDet_eq_const_mul_sq
    (M : PairedGaugeModel) (z : ℂ) :
    M.squareDet (z ^ 2) =
      M.leftConst * M.rightConst * (M.approximant z) ^ 2 := by
  rw [M.squareDet_eq_pair z, M.detMinus_eq z, M.detPlus_eq z]
  exact paired_gauge_product_eq_const_mul_sq
    M.gaugeSlope M.leftConst M.rightConst M.approximant
    M.approximant_even z

/-- A zero of the gauge-cancelled target gives a zero of the squared determinant
at the squared argument. -/
theorem squareDet_eq_zero_of_approximant_eq_zero
    (M : PairedGaugeModel) {z : ℂ}
    (hz : M.approximant z = 0) :
    M.squareDet (z ^ 2) = 0 := by
  rw [M.squareDet_eq_const_mul_sq z, hz]
  ring

/-- If the paired normalization constant is nonzero, zeros of the squared
determinant at squared arguments come only from zeros of the gauge-cancelled
target. -/
theorem approximant_eq_zero_of_squareDet_eq_zero
    (M : PairedGaugeModel) {z : ℂ}
    (hconst : M.leftConst * M.rightConst ≠ 0)
    (hz : M.squareDet (z ^ 2) = 0) :
    M.approximant z = 0 := by
  have hmul : M.leftConst * M.rightConst * (M.approximant z) ^ 2 = 0 := by
    simpa [M.squareDet_eq_const_mul_sq z] using hz
  rcases mul_eq_zero.mp hmul with hnorm | hsquare
  · exact False.elim (hconst hnorm)
  · exact sq_eq_zero_iff.mp hsquare

/-- With nonzero paired normalization, the squared-argument determinant zeros
are exactly the zeros of the gauge-cancelled target. -/
theorem squareDet_sq_eq_zero_iff
    (M : PairedGaugeModel) {z : ℂ}
    (hconst : M.leftConst * M.rightConst ≠ 0) :
    M.squareDet (z ^ 2) = 0 ↔ M.approximant z = 0 := by
  constructor
  · exact M.approximant_eq_zero_of_squareDet_eq_zero hconst
  · exact M.squareDet_eq_zero_of_approximant_eq_zero

end PairedGaugeModel

end SquaredDeterminantGauge
end JensenLadder
