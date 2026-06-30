import GaloisForLFunctions.Core

/-!
# The Li/Bombieri-Lagarias `w`-coordinate (Tier A scalar algebra)

`arakelov-height-of-zeros.md` uses the coordinate `w_ρ = 1 - 1 / ρ` to express the critical
line as the unit circle and the functional-equation pairing `ρ ↔ 1 - ρ` as inversion. This file
formalizes the finite scalar algebra behind that draft:

* the exact norm-square formula `|w(z)|² - 1 = (1 - 2 Re z) / |z|²`;
* the norm-square unit-circle criterion `|w(z)|² = 1 ↔ Re z = 1/2`;
* the pairwise FE product formula `w(z) w(1-z) = 1`.

It does not formalize Hadamard products, global products over zeros, heights, Bogomolov
minimality, Li positivity, or RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The Li/Bombieri-Lagarias coordinate `w(z)=1-1/z`. -/
def wCoordinate (z : ℂ) : ℂ := 1 - z⁻¹

/-- Real part of the `w`-coordinate. -/
lemma wCoordinate_re (z : ℂ) : (wCoordinate z).re = 1 - z.re / Complex.normSq z := by
  simp [wCoordinate, Complex.inv_re]

/-- Imaginary part of the `w`-coordinate. -/
lemma wCoordinate_im (z : ℂ) : (wCoordinate z).im = z.im / Complex.normSq z := by
  simp [wCoordinate, Complex.inv_im]
  ring

/-- The exact norm-square defect in the `w`-coordinate:
`|1-1/z|² - 1 = (1 - 2 Re z) / |z|²`. -/
theorem wCoordinate_normSq_sub_one (z : ℂ) (hz : z ≠ 0) :
    Complex.normSq (wCoordinate z) - 1 = (1 - 2 * z.re) / Complex.normSq z := by
  have hnsq_ne : Complex.normSq z ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hz
  rw [Complex.normSq_apply, wCoordinate_re, wCoordinate_im]
  field_simp [hnsq_ne]
  rw [Complex.normSq_apply]
  ring

/-- The critical line is exactly the norm-square unit circle in the `w`-coordinate. -/
theorem wCoordinate_normSq_eq_one_iff (z : ℂ) (hz : z ≠ 0) :
    Complex.normSq (wCoordinate z) = 1 ↔ z.re = 1 / 2 := by
  have hnsq_ne : Complex.normSq z ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hz
  constructor
  · intro h
    have hsub : Complex.normSq (wCoordinate z) - 1 = 0 := by rw [h, sub_self]
    rw [wCoordinate_normSq_sub_one z hz] at hsub
    field_simp [hnsq_ne] at hsub
    linarith
  · intro h
    have hsub : Complex.normSq (wCoordinate z) - 1 = 0 := by
      rw [wCoordinate_normSq_sub_one z hz, h]
      ring
    linarith

/-- The functional-equation involution `z ↦ 1-z` becomes a product formula in the `w`-coordinate:
`w(z) w(1-z) = 1`. -/
theorem wCoordinate_sigma_mul (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    wCoordinate z * wCoordinate (1 - z) = 1 := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  unfold wCoordinate
  field_simp [hz0, h1z]
  ring

/-- For `z ≠ 0,1`, the `w`-coordinate is nonzero. -/
lemma wCoordinate_ne_zero (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    wCoordinate z ≠ 0 := by
  intro h
  have hmul := wCoordinate_sigma_mul z hz0 hz1
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

/-- The functional-equation involution `z ↦ 1-z` is inversion in the `w`-coordinate. -/
theorem wCoordinate_sigma_eq_inv (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    wCoordinate (1 - z) = (wCoordinate z)⁻¹ := by
  have hmul := wCoordinate_sigma_mul z hz0 hz1
  have hcomm : wCoordinate (1 - z) * wCoordinate z = 1 := by
    rw [mul_comm]
    exact hmul
  exact eq_inv_of_mul_eq_one_left hcomm

end

end GaloisForLFunctions
