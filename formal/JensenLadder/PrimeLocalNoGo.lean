import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Finite-prime local positivity no-go

This file records the elementary sign obstruction behind the missing-diagonal
mechanism for one finite prime.

For `0 < r < 1`, the one-sided local prime kernel after summing the positive
prime powers has the closed form

```text
  K_r(psi) = 2 * r * (cos psi - r) / (1 - 2*r*cos psi + r^2).
```

The full bi-infinite Poisson kernel is positive, but it includes the `m = 0`
diagonal.  Removing that diagonal gives the one-sided kernel `K_r`, and `K_r`
is sign-indefinite.  In particular it is negative at every point with
`cos psi < r`.

This module does not formalize the geometric-series derivation of the closed
form, the explicit formula, a global Weil positivity theorem, or RH.  It only
formalizes the closed-form local sign obstruction.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace PrimeLocalNoGo

/-- Denominator shared by the one-sided prime kernel and the Poisson kernel. -/
noncomputable def primeDenom (r psi : ℝ) : ℝ :=
  1 - 2 * r * Real.cos psi + r ^ 2

/-- Closed-form one-sided local finite-prime kernel. -/
noncomputable def oneSidedPrimeKernel (r psi : ℝ) : ℝ :=
  (2 * r * (Real.cos psi - r)) / primeDenom r psi

/-- Closed-form full Poisson kernel, including the missing `m = 0` diagonal. -/
noncomputable def poissonKernel (r psi : ℝ) : ℝ :=
  (1 - r ^ 2) / primeDenom r psi

/-- For `0 < r < 1`, the shared denominator is strictly positive. -/
theorem primeDenom_pos {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    0 < primeDenom r psi := by
  have hcos : Real.cos psi ≤ 1 := Real.cos_le_one psi
  have hmul : 2 * r * Real.cos psi ≤ 2 * r := by
    nlinarith
  have hsquare : 0 < (1 - r) ^ 2 := by
    apply sq_pos_of_ne_zero
    linarith
  have hden_lower : (1 - r) ^ 2 ≤ primeDenom r psi := by
    unfold primeDenom
    nlinarith
  exact lt_of_lt_of_le hsquare hden_lower

/-- The denominator is nonzero in the prime range `0 < r < 1`. -/
theorem primeDenom_ne_zero {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    primeDenom r psi ≠ 0 :=
  ne_of_gt (primeDenom_pos hr0 hr1)

/--
The one-sided local finite-prime kernel is negative whenever `cos psi < r`.

This is the formal sign obstruction to treating an individual finite prime as a
locally positive contribution after the `m = 0` diagonal has been removed.
-/
theorem oneSidedPrimeKernel_neg_of_cos_lt {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi < r) :
    oneSidedPrimeKernel r psi < 0 := by
  have hnum : 2 * r * (Real.cos psi - r) < 0 := by
    have hpos : 0 < 2 * r := by nlinarith
    have hneg : Real.cos psi - r < 0 := by linarith
    exact mul_neg_of_pos_of_neg hpos hneg
  exact div_neg_of_neg_of_pos hnum (primeDenom_pos hr0 hr1)

/-- At every zero of cosine, the one-sided local prime kernel has a negative value. -/
theorem oneSidedPrimeKernel_neg_of_cos_eq_zero {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hcos : Real.cos psi = 0) :
    oneSidedPrimeKernel r psi < 0 :=
  oneSidedPrimeKernel_neg_of_cos_lt hr0 hr1 (by simpa [hcos] using hr0)

/-- Closed-form value of the one-sided local kernel at a zero of cosine. -/
theorem oneSidedPrimeKernel_eq_neg_two_mul_sq_div_of_cos_eq_zero
    {r psi : ℝ}
    (hcos : Real.cos psi = 0) :
    oneSidedPrimeKernel r psi = - (2 * r ^ 2) / (1 + r ^ 2) := by
  have hden : 1 + r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg r]
  unfold oneSidedPrimeKernel primeDenom
  rw [hcos]
  field_simp [hden]
  ring

/-- The full Poisson kernel is the one-sided prime kernel plus the missing diagonal. -/
theorem poissonKernel_eq_one_add_oneSidedPrimeKernel {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    poissonKernel r psi = 1 + oneSidedPrimeKernel r psi := by
  have hden : primeDenom r psi ≠ 0 := primeDenom_ne_zero hr0 hr1
  unfold poissonKernel oneSidedPrimeKernel
  field_simp [hden]
  unfold primeDenom
  ring

/-- The full Poisson kernel is positive in the prime range `0 < r < 1`. -/
theorem poissonKernel_pos {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    0 < poissonKernel r psi := by
  have hnum : 0 < 1 - r ^ 2 := by
    nlinarith
  exact div_pos hnum (primeDenom_pos hr0 hr1)

/--
The missing diagonal is exactly what separates the positive full Poisson kernel
from the sign-indefinite one-sided prime kernel.
-/
theorem one_add_oneSidedPrimeKernel_pos {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    0 < 1 + oneSidedPrimeKernel r psi := by
  rw [← poissonKernel_eq_one_add_oneSidedPrimeKernel hr0 hr1]
  exact poissonKernel_pos hr0 hr1

end PrimeLocalNoGo
end JensenLadder
