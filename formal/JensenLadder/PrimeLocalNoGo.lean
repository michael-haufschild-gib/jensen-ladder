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

namespace JensenLadder
namespace PrimeLocalNoGo

/-- The local diagonal threshold forced by the deleted prime kernel at `cos psi = 0`. -/
noncomputable def localDiagonalThreshold (r : ℝ) : ℝ :=
  (2 * r ^ 2) / (1 + r ^ 2)

/-- The forced local diagonal threshold is positive for `0 < r`. -/
theorem localDiagonalThreshold_pos {r : ℝ}
    (hr0 : 0 < r) :
    0 < localDiagonalThreshold r := by
  unfold localDiagonalThreshold
  have hnum : 0 < 2 * r ^ 2 := by nlinarith
  have hden : 0 < 1 + r ^ 2 := by nlinarith [sq_nonneg r]
  exact div_pos hnum hden

/-- At a zero of cosine, any smaller diagonal still leaves the deleted kernel negative. -/
theorem diagonal_add_oneSidedPrimeKernel_neg_of_delta_lt_threshold_of_cos_eq_zero
    {r psi delta : ℝ}
    (hcos : Real.cos psi = 0)
    (hdelta : delta < localDiagonalThreshold r) :
    delta + oneSidedPrimeKernel r psi < 0 := by
  unfold localDiagonalThreshold at hdelta
  rw [oneSidedPrimeKernel_eq_neg_two_mul_sq_div_of_cos_eq_zero hcos]
  have heq : delta + -(2 * r ^ 2) / (1 + r ^ 2)
      = delta - (2 * r ^ 2) / (1 + r ^ 2) := by ring
  rw [heq]
  exact sub_neg.mpr hdelta

/-- The same lower-bound obstruction at `psi = pi/2`. -/
theorem diagonal_add_oneSidedPrimeKernel_neg_of_delta_lt_threshold_at_pi_div_two
    {r delta : ℝ}
    (hdelta : delta < localDiagonalThreshold r) :
    delta + oneSidedPrimeKernel r (Real.pi / 2) < 0 := by
  exact diagonal_add_oneSidedPrimeKernel_neg_of_delta_lt_threshold_of_cos_eq_zero
    (r := r) (psi := Real.pi / 2) (delta := delta)
    (by simp) hdelta

/-- A diagonal below the threshold cannot make the deleted kernel nonnegative everywhere. -/
theorem not_forall_nonnegative_diagonal_add_oneSidedPrimeKernel_of_delta_lt_threshold
    {r delta : ℝ}
    (hdelta : delta < localDiagonalThreshold r) :
    ¬ (∀ psi : ℝ, 0 <= delta + oneSidedPrimeKernel r psi) := by
  intro hnonneg
  have hneg := diagonal_add_oneSidedPrimeKernel_neg_of_delta_lt_threshold_at_pi_div_two
    (r := r) (delta := delta) hdelta
  have hnon := hnonneg (Real.pi / 2)
  linarith

end PrimeLocalNoGo
end JensenLadder

namespace JensenLadder
namespace PrimeLocalNoGo

/-- The exact uniform local diagonal threshold for the deleted prime kernel. -/
noncomputable def uniformLocalDiagonalThreshold (r : ℝ) : ℝ :=
  (2 * r) / (1 + r)

/-- The uniform local threshold is positive in the prime range. -/
theorem uniformLocalDiagonalThreshold_pos {r : ℝ}
    (hr0 : 0 < r) :
    0 < uniformLocalDiagonalThreshold r := by
  unfold uniformLocalDiagonalThreshold
  have hnum : 0 < 2 * r := by nlinarith
  have hden : 0 < 1 + r := by nlinarith
  exact div_pos hnum hden

/-- The uniform local threshold is smaller than the full missing diagonal `1`. -/
theorem uniformLocalDiagonalThreshold_lt_one {r : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    uniformLocalDiagonalThreshold r < 1 := by
  unfold uniformLocalDiagonalThreshold
  have hden : 0 < 1 + r := by nlinarith
  rw [div_lt_one hden]
  nlinarith

/-- Adding the uniform threshold makes the deleted one-prime kernel nonnegative at every phase. -/
theorem uniformLocalDiagonalThreshold_add_oneSidedPrimeKernel_nonnegative
    {r psi : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    0 <= uniformLocalDiagonalThreshold r + oneSidedPrimeKernel r psi := by
  have hdenpos : 0 < primeDenom r psi := primeDenom_pos hr0 hr1
  have hdenne : primeDenom r psi ≠ 0 := ne_of_gt hdenpos
  have h1pos : 0 < 1 + r := by nlinarith
  have h1ne : 1 + r ≠ 0 := ne_of_gt h1pos
  have hcos : -1 <= Real.cos psi := Real.neg_one_le_cos psi
  have hnum : 0 <= 2 * r * ((1 - r) * (1 + Real.cos psi)) := by
    have h2r : 0 <= 2 * r := by nlinarith
    have h1r : 0 <= 1 - r := by nlinarith
    have h1c : 0 <= 1 + Real.cos psi := by linarith
    positivity
  have hdenprod : 0 < (1 + r) * primeDenom r psi := mul_pos h1pos hdenpos
  have hfrac : 0 <= (2 * r * ((1 - r) * (1 + Real.cos psi))) /
      ((1 + r) * primeDenom r psi) := div_nonneg hnum (le_of_lt hdenprod)
  have heq : uniformLocalDiagonalThreshold r + oneSidedPrimeKernel r psi =
      (2 * r * ((1 - r) * (1 + Real.cos psi))) /
        ((1 + r) * primeDenom r psi) := by
    unfold uniformLocalDiagonalThreshold oneSidedPrimeKernel
    field_simp [h1ne, hdenne]
    unfold primeDenom
    ring
  rw [heq]
  exact hfrac

/-- At `psi = pi`, the deleted kernel reaches the negative of the uniform threshold. -/
theorem oneSidedPrimeKernel_eq_neg_uniformLocalDiagonalThreshold_at_pi
    {r : ℝ}
    (hr0 : 0 < r) :
    oneSidedPrimeKernel r Real.pi = - uniformLocalDiagonalThreshold r := by
  have h1ne : 1 + r ≠ 0 := by nlinarith
  have hsqne : (1 + r) ^ 2 ≠ 0 := pow_ne_zero 2 h1ne
  unfold oneSidedPrimeKernel primeDenom uniformLocalDiagonalThreshold
  rw [Real.cos_pi]
  have hdeneq : 1 - 2 * r * -1 + r ^ 2 = (1 + r) ^ 2 := by ring
  rw [hdeneq]
  field_simp [h1ne, hsqne]
  ring

/-- The exact uniform local diagonal criterion for the deleted one-prime kernel. -/
theorem forall_nonnegative_diagonal_add_oneSidedPrimeKernel_iff_uniformThreshold_le_delta
    {r delta : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    (∀ psi : ℝ, 0 <= delta + oneSidedPrimeKernel r psi) ↔
      uniformLocalDiagonalThreshold r <= delta := by
  constructor
  · intro hnon
    have hpi := hnon Real.pi
    rw [oneSidedPrimeKernel_eq_neg_uniformLocalDiagonalThreshold_at_pi (r := r) hr0] at hpi
    linarith
  · intro hdelta psi
    have hbase := uniformLocalDiagonalThreshold_add_oneSidedPrimeKernel_nonnegative
      (r := r) (psi := psi) hr0 hr1
    linarith

/-- Any diagonal below the exact uniform threshold fails at some phase. -/
theorem not_forall_nonnegative_diagonal_add_oneSidedPrimeKernel_of_delta_lt_uniformThreshold
    {r delta : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1)
    (hdelta : delta < uniformLocalDiagonalThreshold r) :
    ¬ (∀ psi : ℝ, 0 <= delta + oneSidedPrimeKernel r psi) := by
  intro hnon
  have hle := (forall_nonnegative_diagonal_add_oneSidedPrimeKernel_iff_uniformThreshold_le_delta
    (r := r) (delta := delta) hr0 hr1).1 hnon
  linarith

end PrimeLocalNoGo
end JensenLadder

namespace JensenLadder
namespace PrimeLocalNoGo

/-- The exact local threshold dominates the square scale `r^2`. -/
theorem sq_le_uniformLocalDiagonalThreshold {r : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    r ^ 2 <= uniformLocalDiagonalThreshold r := by
  unfold uniformLocalDiagonalThreshold
  have hden : 0 < 1 + r := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith

/-- In the prime range, the exact local threshold strictly dominates `r^2`. -/
theorem sq_lt_uniformLocalDiagonalThreshold {r : ℝ}
    (hr0 : 0 < r)
    (hr1 : r < 1) :
    r ^ 2 < uniformLocalDiagonalThreshold r := by
  unfold uniformLocalDiagonalThreshold
  have hden : 0 < 1 + r := by nlinarith
  rw [lt_div_iff₀ hden]
  have hpos : 0 < r * (1 - r) * (1 + r) := by positivity
  nlinarith

/-- Finite packets inherit the threshold lower bound term by term. -/
theorem sum_sq_le_sum_uniformLocalDiagonalThreshold {α : Type*}
    (s : Finset α) (r : α -> ℝ)
    (hr0 : ∀ a ∈ s, 0 < r a)
    (hr1 : ∀ a ∈ s, r a < 1) :
    (∑ a ∈ s, r a ^ 2) <= ∑ a ∈ s, uniformLocalDiagonalThreshold (r a) := by
  exact Finset.sum_le_sum fun a ha =>
    sq_le_uniformLocalDiagonalThreshold (hr0 a ha) (hr1 a ha)

end PrimeLocalNoGo
end JensenLadder
