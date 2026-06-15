import Mathlib

/-!
# Li's criterion in the disk coordinate `w = 1 − 1/ρ` — formalized geometric + positivity core

A sustained attack on the **Li-criterion / disk** face of W3 (one of the eight RH-equivalent faces;
`docs/rh/w3_wall_five_attacks_20260615.md`). Li (1997)/Bombieri–Lagarias:
`RH ⟺ λ_n := Σ_ρ (1 − (1−1/ρ)ⁿ) ≥ 0 ∀ n`, via the Möbius map `ρ ↦ w_ρ = 1 − 1/ρ`.

This file formalizes the **geometric heart and the easy-direction kernel** (the hard direction,
`λ_n ≥ 0 ∀n ⟹ RH`, is Li's deep theorem and is NOT proved here):

* `norm_one_sub_inv_eq_one_iff` — the Möbius map sends the critical line exactly to the unit circle:
  `‖1 − 1/ρ‖ = 1 ⟺ Re ρ = ½`.
* `mobius_one_sub_eq_inv` — the functional equation `ρ ↔ 1−ρ` becomes circle inversion `w ↔ 1/w`:
  `1 − 1/(1−ρ) = 1/(1 − 1/ρ)`.
* `li_pair_summand_nonneg` — the easy-direction kernel: for a critical-line zero (`‖w‖=1`), the
  Li pair-summand `(1−wⁿ) + (1−w̄ⁿ) = 2 − 2 Re(wⁿ) ≥ 0`, since `Re(wⁿ) ≤ ‖wⁿ‖ = 1`.

Together: **on the critical line the Li coefficients are sums of non-negative pair-summands**
(RH ⟹ `λ_n ≥ 0`, the easy half). RH-agnostic facts about the Möbius coordinate; Theorem M does not
prove RH by itself.
-/

open Complex

namespace LiCriterionDisk

/-- **Möbius: critical line ↔ unit circle.** `‖1 − 1/ρ‖ = 1 ⟺ Re ρ = ½` (for `ρ ≠ 0`). The map
`ρ ↦ 1 − 1/ρ = (ρ−1)/ρ` has unit modulus iff `‖ρ−1‖ = ‖ρ‖`, i.e. `ρ` is equidistant from `0` and `1`,
i.e. `Re ρ = ½`. -/
theorem norm_one_sub_inv_eq_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hstep : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [hstep, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hρ)]
  have key : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 ↔ ρ.re = 1 / 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro h; exact key.mp (by rw [h])
  · intro h
    have h2 := key.mpr h
    rw [← Real.sqrt_sq (norm_nonneg (ρ - 1)), ← Real.sqrt_sq (norm_nonneg ρ), h2]

/-- **Möbius: right half-plane ↔ open unit disk.** `‖1 − 1/ρ‖ < 1 ⟺ Re ρ > ½` (for `ρ ≠ 0`). So a
zero strictly right of the critical line maps strictly *inside* the unit disk (and, by the FE
inversion `w↔1/w`, its partner maps strictly outside). This is the geometric setup of the *hard*
direction of Li's criterion: an off-line zero produces an off-circle `w`, whose `wⁿ` (modulus `≠1`)
drives the Li coefficient negative for some `n`. -/
theorem norm_one_sub_inv_lt_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ < 1 ↔ 1 / 2 < ρ.re := by
  have hstep : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [hstep, norm_div, div_lt_one (norm_pos_iff.mpr hρ)]
  constructor
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
    nlinarith [h2]
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
      nlinarith [h]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-- **Functional equation = circle inversion.** Under `w = 1 − 1/ρ`, the reflection `ρ ↔ 1−ρ` becomes
`w ↔ 1/w`: `1 − 1/(1−ρ) = 1/(1 − 1/ρ)` (for `ρ ≠ 0, 1`); both sides equal `ρ/(ρ−1)`. So zeros sit in
quadruples `{w, w̄, 1/w, 1/w̄}`, collapsing to circle-pairs `{w, w̄}` exactly on `‖w‖=1` (= RH). -/
theorem mobius_one_sub_eq_inv {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    1 - 1 / (1 - ρ) = 1 / (1 - 1 / ρ) := by
  have hsub : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (fun h => h1 h.symm)
  have hsub2 : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hwz : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  have L : 1 - 1 / (1 - ρ) = ρ / (ρ - 1) := by
    rw [eq_div_iff hsub2]; field_simp; ring
  rw [L, hwz, one_div_div]

/-- **Easy-direction kernel.** For a critical-line zero (its image `w = 1−1/ρ` has `‖w‖ = 1`), the Li
pair-summand `(1 − wⁿ) + (1 − w̄ⁿ) = 2 − 2 Re(wⁿ)` is `≥ 0`, because `Re(wⁿ) ≤ ‖wⁿ‖ = ‖w‖ⁿ = 1`. So
under RH every Li pair-summand is non-negative ⟹ `λ_n ≥ 0` (the easy half of Li's criterion). -/
theorem li_pair_summand_nonneg {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ 2 - 2 * (w ^ n).re := by
  have hre : (w ^ n).re ≤ 1 := by
    calc (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
      _ = ‖w‖ ^ n := by rw [norm_pow]
      _ = 1 := by rw [hw, one_pow]
  linarith

/-- **Easy direction, abstract form.** For any family `w : ι → ℂ` of unit-modulus points (the Möbius
images of critical-line zeros), the `n`-th Li coefficient `λ_n = ∑ᵢ (2 − 2 Re(wᵢⁿ))` is `≥ 0`. This is
`RH ⟹ λ_n ≥ 0` in abstract form: each pair-summand is `≥0` (`li_pair_summand_nonneg`), so the sum is `≥0`
by `tsum_nonneg`. (No summability needed: a non-summable `tsum` is `0 ≥ 0`.) Instantiating `wᵢ = 1 − 1/ρᵢ`
with `Re ρᵢ = ½` (via `norm_one_sub_inv_eq_one_iff`) gives the easy half of Li's criterion for `ξ`. -/
theorem li_coefficient_nonneg_of_unit_modulus {ι : Type*} (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) (n : ℕ) :
    0 ≤ ∑' i, (2 - 2 * (w i ^ n).re) :=
  tsum_nonneg (fun i => li_pair_summand_nonneg (hw i) n)

end LiCriterionDisk
