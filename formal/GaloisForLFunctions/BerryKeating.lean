import GaloisForLFunctions.Core

/-!
# The Berry-Keating `u = s(1-s)` coordinate (Tier A scalar skeleton)

This file formalizes the elementary algebra behind the FE-invariant coordinate
used in the Hilbert-Polya/Berry-Keating reading:

* `u(s) = s(1-s)` is invariant under the functional-equation involution
  `s ↦ 1-s`;
* on the critical line `s = 1/2 + iγ`, it is exactly the real value
  `1/4 + γ^2`, hence at least `1/4`;
* for a point with nonzero imaginary part away from the critical line, `u(s)`
  has nonzero imaginary part.

This is only scalar complex arithmetic. It does not construct a Hilbert-Polya
operator, prove self-adjointness, identify spectra, or prove RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The FE-invariant Berry-Keating coordinate `u = s(1-s)`. -/
def berryKeatingU (s : ℂ) : ℂ := s * (1 - s)

@[simp] theorem berryKeatingU_apply (s : ℂ) : berryKeatingU s = s * (1 - s) := rfl

/-- The coordinate `u=s(1-s)` is invariant under the functional-equation involution. -/
theorem berryKeatingU_sigma (s : ℂ) : berryKeatingU (sigma s) = berryKeatingU s := by
  simp [berryKeatingU, sigma]
  ring

/-- Real part of the Berry-Keating coordinate in rectangular coordinates. -/
theorem berryKeatingU_re (s : ℂ) :
    (berryKeatingU s).re = s.re * (1 - s.re) + s.im ^ 2 := by
  simp [berryKeatingU, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- Imaginary part of the Berry-Keating coordinate in rectangular coordinates. -/
theorem berryKeatingU_im (s : ℂ) :
    (berryKeatingU s).im = (1 - 2 * s.re) * s.im := by
  simp [berryKeatingU, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- On the critical line, `u=s(1-s)` is real and equals `1/4 + Im(s)^2`. -/
theorem berryKeatingU_on_critical (s : ℂ) (hs : s.re = 1 / 2) :
    (berryKeatingU s).im = 0 ∧ (berryKeatingU s).re = 1 / 4 + s.im ^ 2 := by
  constructor
  · rw [berryKeatingU_im, hs]
    ring
  · rw [berryKeatingU_re, hs]
    ring

/-- On the critical line, the real `u`-coordinate lies on the ray `[1/4,∞)`. -/
theorem berryKeatingU_re_ge_quarter_on_critical (s : ℂ) (hs : s.re = 1 / 2) :
    1 / 4 ≤ (berryKeatingU s).re := by
  rw [(berryKeatingU_on_critical s hs).2]
  nlinarith [sq_nonneg s.im]

/-- Parametrized critical-line formula: `u(1/2+iγ)=1/4+γ^2`. -/
theorem berryKeatingU_critical_param (γ : ℝ) :
    berryKeatingU ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = (1 / 4 + γ ^ 2 : ℂ) := by
  apply Complex.ext
  · rw [berryKeatingU_re]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_cast
    ring
  · rw [berryKeatingU_im]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_cast

/-- A non-real point away from the critical line maps to a non-real `u`-coordinate.
The `s.im ≠ 0` hypothesis is essential: real off-line points still have real `u`. -/
theorem berryKeatingU_nonreal_of_offCritical_nonzero_im (s : ℂ)
    (hcrit : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    (berryKeatingU s).im ≠ 0 := by
  rw [berryKeatingU_im]
  apply mul_ne_zero
  · intro h
    apply hcrit
    linarith
  · exact him

end

end GaloisForLFunctions
