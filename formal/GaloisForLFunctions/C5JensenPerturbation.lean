import Mathlib

/-!
# C5 Jensen perturbation infrastructure

This file formalizes reusable real-analysis pieces from the
`c5-jensen-perturbation-lemma` card.  In particular, it covers the
zero-slope closed-interval witness branch and the IVT/sign-transfer steps used
by the localized perturbation proof.
-/

namespace GaloisForLFunctions

noncomputable section

/-- If a perturbation derivative has zero sup-bound on a window containing the center,
then the perturbation derivative vanishes at the center. -/
theorem windowSlope_zero_at_center {D' : ℝ → ℝ} {x w : ℝ}
    (hw : 0 ≤ w)
    (hD : ∀ y, |y - x| ≤ w → |D' y| ≤ 0) :
    D' x = 0 := by
  have hx : |x - x| ≤ w := by simpa using hw
  have hDx : |D' x| ≤ 0 := hD x hx
  exact abs_eq_zero.mp (le_antisymm hDx (abs_nonneg (D' x)))

/-- The zero-slope branch of the localized Jensen perturbation witness: if `ε = 0`,
`C' x = 0`, and the perturbation derivative has zero bound on a window containing `x`,
then the closed interval `[x - ε, x + ε]` contains a zero of the derivative of `C + D`. -/
theorem jensenClosedWitness_of_zeroEpsilon {C' D' : ℝ → ℝ} {x w ε : ℝ}
    (hε : ε = 0)
    (hw : 0 ≤ w)
    (hC : C' x = 0)
    (hD : ∀ y, |y - x| ≤ w → |D' y| ≤ 0) :
    ∃ x', x' ∈ Set.Icc (x - ε) (x + ε) ∧ C' x' + D' x' = 0 := by
  refine ⟨x, ?_, ?_⟩
  · subst ε
    simp
  · have hDx : D' x = 0 := windowSlope_zero_at_center (D' := D') hw hD
    simp [hC, hDx]

/-- Membership in the closed symmetric interval `[x - ε, x + ε]` gives the distance
bound used by the total-witness perturbation lemma. -/
theorem abs_sub_center_le_of_mem_Icc_sub_add {x ε x' : ℝ}
    (hx' : x' ∈ Set.Icc (x - ε) (x + ε)) :
    |x' - x| ≤ ε := by
  rw [abs_le]
  constructor <;> linarith [hx'.1, hx'.2]

/-- IVT bridge for the positive orientation: a continuous function on `[a,b]` with
opposite weak endpoint signs has a zero in `[a,b]`. -/
theorem exists_zero_Icc_of_nonpos_of_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a ≤ 0)
    (hb : 0 ≤ f b) :
    ∃ c, c ∈ Set.Icc a b ∧ f c = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hf hzero with ⟨c, hc, hfc⟩
  exact ⟨c, hc, hfc⟩

/-- IVT bridge for the negative orientation: a continuous function on `[a,b]` with
opposite weak endpoint signs has a zero in `[a,b]`. -/
theorem exists_zero_Icc_of_nonneg_of_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (ha : 0 ≤ f a)
    (hb : f b ≤ 0) :
    ∃ c, c ∈ Set.Icc a b ∧ f c = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨hb, ha⟩
  rcases intermediate_value_Icc' hab hf hzero with ⟨c, hc, hfc⟩
  exact ⟨c, hc, hfc⟩

/-- If an unperturbed endpoint value is at most `-B` and the perturbation has
absolute value at most `B`, their sum is nonpositive. -/
theorem add_nonpos_of_le_neg_bound_of_abs_le {c d B : ℝ}
    (hc : c ≤ -B)
    (hd : |d| ≤ B) :
    c + d ≤ 0 := by
  have hd_upper : d ≤ B := (abs_le.mp hd).2
  linarith

/-- If an unperturbed endpoint value is at least `B` and the perturbation has
absolute value at most `B`, their sum is nonnegative. -/
theorem add_nonneg_of_bound_le_of_abs_le {c d B : ℝ}
    (hc : B ≤ c)
    (hd : |d| ≤ B) :
    0 ≤ c + d := by
  have hd_lower : -B ≤ d := (abs_le.mp hd).1
  linarith

/-- Positive-orientation endpoint dominance plus IVT. This packages the step where
`F' = C' + D'` has weak opposite signs at the two endpoints because `|D'|` is
bounded by the endpoint lower bound for `|C'|`. -/
theorem exists_zero_Icc_of_endpoint_abs_bounds_pos {C' D' : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun y => C' y + D' y) (Set.Icc a b))
    (hCa : C' a ≤ -B)
    (hCb : B ≤ C' b)
    (hDa : |D' a| ≤ B)
    (hDb : |D' b| ≤ B) :
    ∃ c, c ∈ Set.Icc a b ∧ C' c + D' c = 0 := by
  have ha : C' a + D' a ≤ 0 := add_nonpos_of_le_neg_bound_of_abs_le hCa hDa
  have hb : 0 ≤ C' b + D' b := add_nonneg_of_bound_le_of_abs_le hCb hDb
  exact exists_zero_Icc_of_nonpos_of_nonneg hab hcont ha hb

/-- Negative-orientation endpoint dominance plus IVT. -/
theorem exists_zero_Icc_of_endpoint_abs_bounds_neg {C' D' : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun y => C' y + D' y) (Set.Icc a b))
    (hCa : B ≤ C' a)
    (hCb : C' b ≤ -B)
    (hDa : |D' a| ≤ B)
    (hDb : |D' b| ≤ B) :
    ∃ c, c ∈ Set.Icc a b ∧ C' c + D' c = 0 := by
  have ha : 0 ≤ C' a + D' a := add_nonneg_of_bound_le_of_abs_le hCa hDa
  have hb : C' b + D' b ≤ 0 := add_nonpos_of_le_neg_bound_of_abs_le hCb hDb
  exact exists_zero_Icc_of_nonneg_of_nonpos hab hcont ha hb

/-- If endpoint values have strictly opposite signs, IVT gives a zero in the closed
interval between them. -/
theorem exists_zero_Icc_of_endpoint_product_neg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hprod : f a * f b < 0) :
    ∃ c, c ∈ Set.Icc a b ∧ f c = 0 := by
  rcases (mul_neg_iff.mp hprod) with hposneg | hnegpos
  · exact exists_zero_Icc_of_nonneg_of_nonpos hab hf hposneg.1.le hposneg.2.le
  · exact exists_zero_Icc_of_nonpos_of_nonneg hab hf hnegpos.1.le hnegpos.2.le

/-- If a real perturbation is closer to `c` than `c` is to zero, then it has the same
strict sign as `c`, encoded as a positive product. -/
theorem same_sign_product_pos_of_abs_sub_lt_abs {y c : ℝ}
    (h : |y - c| < |c|) :
    0 < y * c := by
  have hc_ne : c ≠ 0 := by
    intro hc
    have hy : |y| < 0 := by simpa [hc] using h
    exact (not_lt_of_ge (abs_nonneg y)) hy
  rcases lt_or_gt_of_ne hc_ne with hcneg | hcpos
  · have hlt := (abs_lt.mp h).2
    have hlt' : y - c < -c := by simpa [abs_of_neg hcneg] using hlt
    have hyneg : y < 0 := by linarith
    nlinarith
  · have hlt := (abs_lt.mp h).1
    have hlt' : -c < y - c := by simpa [abs_of_pos hcpos] using hlt
    have hypos : 0 < y := by linarith
    nlinarith

/-- If two values have the same strict signs as two reference values, and the reference
values have opposite signs, then the two values have opposite signs. -/
theorem opposite_sign_product_neg_of_same_sign_products {y z c d : ℝ}
    (hy : 0 < y * c)
    (hz : 0 < z * d)
    (hcd : c * d < 0) :
    y * z < 0 := by
  have hprod : 0 < (y * c) * (z * d) := mul_pos hy hz
  have hfactor : (y * c) * (z * d) = (y * z) * (c * d) := by ring
  rw [hfactor] at hprod
  by_contra hnot
  have hyz_nonneg : 0 ≤ y * z := le_of_not_gt hnot
  nlinarith

/-- The absolute-closeness form of sign transfer for two adjacent critical values. -/
theorem opposite_sign_product_neg_of_abs_sub_lt_abs {y z c d : ℝ}
    (hy : |y - c| < |c|)
    (hz : |z - d| < |d|)
    (hcd : c * d < 0) :
    y * z < 0 := by
  exact opposite_sign_product_neg_of_same_sign_products
    (same_sign_product_pos_of_abs_sub_lt_abs hy)
    (same_sign_product_pos_of_abs_sub_lt_abs hz)
    hcd

end

end GaloisForLFunctions
