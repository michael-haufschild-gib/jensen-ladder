import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# BAH1 quadratic scale-lock algebra

This file formalizes the route-control algebra for the `BAH1` direct
Suzuki/ScrewHat candidate.  It does not prove a packet-to-prime theorem; it
only proves the residual-minimal kill screen for a fixed pre-sign quadratic
direction.

For a fixed projective direction `w`, write the quadratic observable as

```text
U_Q(sqrt rho * w) = rho * A
```

with nonnegative total homogeneous debt `rho * D`, packet value `NB = -nB`, and
packet margin `MB`.  Any actual comparison must pay at least

```text
|rho * A + nB| + rho * D.
```

If `nB >= MB > 0`, a strict margin can occur only when `A < 0` and `D < -A`.

## Honest scope

This is a proved algebraic feasibility screen for one candidate row.  The
arithmetic forcing row, the independent lower row, the legal pre-sign selector,
and the fake-family failure remain open.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

namespace JensenLadder
namespace BAH1Quadratic

/-- If the fixed quadratic direction has nonnegative coefficient, then no
nonnegative amplitude can beat the bad-packet margin, even under the
residual-minimal debt model. -/
theorem residual_margin_impossible_of_nonnegative_direction
    {A D nB MB rho : ℝ}
    (hMB_pos : 0 < MB)
    (hnB : MB ≤ nB)
    (hrho : 0 ≤ rho)
    (hA_nonneg : 0 ≤ A)
    (hD_nonneg : 0 ≤ D) :
    ¬ |rho * A + nB| + rho * D < MB := by
  intro hmargin
  have hnB_nonneg : 0 ≤ nB := le_trans (le_of_lt hMB_pos) hnB
  have hprodA_nonneg : 0 ≤ rho * A := mul_nonneg hrho hA_nonneg
  have hsum_nonneg : 0 ≤ rho * A + nB := by
    nlinarith
  have hprodD_nonneg : 0 ≤ rho * D := mul_nonneg hrho hD_nonneg
  rw [abs_of_nonneg hsum_nonneg] at hmargin
  nlinarith

/-- If the debt dominates a negative quadratic coefficient (`D >= -A`), then
no nonnegative amplitude can beat the bad-packet margin, even under the
residual-minimal debt model. -/
theorem residual_margin_impossible_of_debt_dominated_direction
    {A D nB MB rho : ℝ}
    (_hMB_pos : 0 < MB)
    (hnB : MB ≤ nB)
    (hrho : 0 ≤ rho)
    (hD_ge : -A ≤ D) :
    ¬ |rho * A + nB| + rho * D < MB := by
  intro hmargin
  have habs : nB + rho * A ≤ |rho * A + nB| := by
    calc
      nB + rho * A = rho * A + nB := by ring
      _ ≤ |rho * A + nB| := le_abs_self _
  have hmulD : rho * (-A) ≤ rho * D :=
    mul_le_mul_of_nonneg_left hD_ge hrho
  have hlower : nB ≤ |rho * A + nB| + rho * D := by
    nlinarith
  nlinarith

/-- A strict residual-minimal BAH1 quadratic margin forces a genuinely negative
direction whose magnitude exceeds the homogeneous debt. -/
theorem negative_direction_and_debt_gap_of_residual_margin
    {A D nB MB rho : ℝ}
    (hMB_pos : 0 < MB)
    (hnB : MB ≤ nB)
    (hrho : 0 ≤ rho)
    (hD_nonneg : 0 ≤ D)
    (hmargin : |rho * A + nB| + rho * D < MB) :
    A < 0 ∧ D < -A := by
  have hA_neg : A < 0 := by
    by_contra hnot
    exact residual_margin_impossible_of_nonnegative_direction
      hMB_pos hnB hrho (le_of_not_gt hnot) hD_nonneg hmargin
  have hD_gap : D < -A := by
    by_contra hnot
    exact residual_margin_impossible_of_debt_dominated_direction
      hMB_pos hnB hrho (le_of_not_gt hnot) hmargin
  exact ⟨hA_neg, hD_gap⟩

/-- At the packet-canceling amplitude `rho = nB / (-A)`, a negative quadratic
direction has residual value exactly `nB * D / (-A)`. -/
theorem residual_value_at_packet_canceling_amplitude
    {A D nB : ℝ}
    (hA_neg : A < 0) :
    |(nB / (-A)) * A + nB| + (nB / (-A)) * D = nB * D / (-A) := by
  have hA_ne : A ≠ 0 := ne_of_lt hA_neg
  have hzero : nB / (-A) * A + nB = 0 := by
    field_simp [hA_ne]
    ring
  have hprod : nB / (-A) * D = nB * D / (-A) := by
    ring
  rw [hzero, abs_zero, zero_add, hprod]

/-- For a negative direction whose magnitude beats the debt, the
packet-canceling residual value is a global lower bound for the residual-minimal
quadratic margin expression. -/
theorem residual_value_lower_bound_of_negative_direction_debt_gap
    {A D nB rho : ℝ}
    (hA_neg : A < 0)
    (hD_nonneg : 0 ≤ D)
    (hD_gap : D < -A) :
    nB * D / (-A) ≤ |rho * A + nB| + rho * D := by
  have hden_pos : 0 < -A := by linarith
  have hA_ne : A ≠ 0 := ne_of_lt hA_neg
  by_cases hle : rho ≤ nB / (-A)
  · have hdist_nonneg : 0 ≤ nB / (-A) - rho := by linarith
    have hgap_nonneg : 0 ≤ -A - D := by linarith
    have hmul_nonneg : 0 ≤ (-A - D) * (nB / (-A) - rho) :=
      mul_nonneg hgap_nonneg hdist_nonneg
    have hsum_nonneg : 0 ≤ rho * A + nB := by
      have hmul : rho * (-A) ≤ (nB / (-A)) * (-A) :=
        mul_le_mul_of_nonneg_right hle (le_of_lt hden_pos)
      have hcancel : (nB / (-A)) * (-A) = nB := by
        field_simp [ne_of_gt hden_pos]
      rw [hcancel] at hmul
      nlinarith
    rw [abs_of_nonneg hsum_nonneg]
    have hidentity :
        (rho * A + nB + rho * D) - nB * D / (-A) =
          (-A - D) * (nB / (-A) - rho) := by
      field_simp [hA_ne]
      ring
    nlinarith [hidentity, hmul_nonneg]
  · have hge : nB / (-A) ≤ rho := le_of_not_ge hle
    have hdist_nonneg : 0 ≤ rho - nB / (-A) := by linarith
    have hcoef_nonneg : 0 ≤ -A + D := by linarith [hden_pos, hD_nonneg]
    have hmul_nonneg : 0 ≤ (-A + D) * (rho - nB / (-A)) :=
      mul_nonneg hcoef_nonneg hdist_nonneg
    have hsum_nonpos : rho * A + nB ≤ 0 := by
      have hmul : (nB / (-A)) * (-A) ≤ rho * (-A) :=
        mul_le_mul_of_nonneg_right hge (le_of_lt hden_pos)
      have hcancel : (nB / (-A)) * (-A) = nB := by
        field_simp [ne_of_gt hden_pos]
      rw [hcancel] at hmul
      nlinarith
    rw [abs_of_nonpos hsum_nonpos]
    have hidentity :
        (-(rho * A + nB) + rho * D) - nB * D / (-A) =
          (-A + D) * (rho - nB / (-A)) := by
      field_simp [hA_ne]
      ring
    nlinarith [hidentity, hmul_nonneg]

/-- Exact residual-minimal value for a negative BAH1 quadratic direction whose
coefficient magnitude beats the homogeneous debt. -/
theorem residual_minimum_value_of_negative_direction_debt_gap
    {A D nB : ℝ}
    (hA_neg : A < 0)
    (hD_nonneg : 0 ≤ D)
    (hD_gap : D < -A) :
    (∀ rho : ℝ, nB * D / (-A) ≤ |rho * A + nB| + rho * D) ∧
      |(nB / (-A)) * A + nB| + (nB / (-A)) * D = nB * D / (-A) := by
  exact ⟨
    fun rho => residual_value_lower_bound_of_negative_direction_debt_gap
      hA_neg hD_nonneg hD_gap,
    residual_value_at_packet_canceling_amplitude hA_neg⟩

/-- The packet-canceling amplitude is legal as a nonnegative quadratic scale
when `nB >= 0` and the direction is negative. -/
theorem packet_canceling_amplitude_nonneg
    {A nB : ℝ}
    (hA_neg : A < 0)
    (hnB_nonneg : 0 ≤ nB) :
    0 ≤ nB / (-A) := by
  have hden_pos : 0 < -A := by linarith
  exact div_nonneg hnB_nonneg (le_of_lt hden_pos)

/-- If the negative direction beats the ratio screen, the packet-canceling
amplitude realizes a strict residual-minimal margin. -/
theorem exists_residual_margin_of_negative_direction_ratio
    {A D nB MB : ℝ}
    (hA_neg : A < 0)
    (hnB_nonneg : 0 ≤ nB)
    (hratio : nB * D / (-A) < MB) :
    ∃ rho : ℝ, 0 ≤ rho ∧ |rho * A + nB| + rho * D < MB := by
  refine ⟨nB / (-A), ?_, ?_⟩
  · exact packet_canceling_amplitude_nonneg hA_neg hnB_nonneg
  · rw [residual_value_at_packet_canceling_amplitude hA_neg]
    exact hratio

/-- Any strict quadratic PacketForce margin with an additive non-adaptive error
floor forces that floor to be strictly below the packet margin.  This is the
formal criticality screen: a fixed positive floor cannot exclude arbitrarily
small bad-packet margins. -/
theorem error_floor_lt_margin_of_residual_margin
    {A D nB MB Efloor rho : ℝ}
    (hrho : 0 ≤ rho)
    (hD_nonneg : 0 ≤ D)
    (hmargin : |rho * A + nB| + rho * D + Efloor < MB) :
    Efloor < MB := by
  have hres_nonneg : 0 ≤ |rho * A + nB| + rho * D := by
    have hDterm : 0 ≤ rho * D := mul_nonneg hrho hD_nonneg
    exact add_nonneg (abs_nonneg _) hDterm
  linarith

/-- If a non-adaptive additive error floor is at least the packet margin, the
strict quadratic margin is impossible. -/
theorem residual_margin_impossible_of_error_floor_ge_margin
    {A D nB MB Efloor rho : ℝ}
    (hrho : 0 ≤ rho)
    (hD_nonneg : 0 ≤ D)
    (hfloor : MB ≤ Efloor) :
    ¬ |rho * A + nB| + rho * D + Efloor < MB := by
  intro hmargin
  have hEfloor_lt : Efloor < MB :=
    error_floor_lt_margin_of_residual_margin hrho hD_nonneg hmargin
  linarith

/-- A fixed positive additive floor cannot certify a family of positive packet
margins that is arbitrarily small.  This packages the criticality obstruction in
the abstract form needed by the BAH1 no-go ledger: if some bad-packet margins
fall below every positive scale, then one of them is below any fixed positive
non-adaptive floor, so strict margin is impossible there. -/
theorem exists_margin_index_impossible_of_arbitrarily_small_margins
    {ι : Type} {MB : ι → ℝ} {Efloor : ℝ}
    (hEfloor_pos : 0 < Efloor)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ i : ι, 0 < MB i ∧ MB i ≤ eps) :
    ∃ i : ι, 0 < MB i ∧
      ∀ A D nB rho : ℝ,
        0 ≤ rho →
        0 ≤ D →
        ¬ |rho * A + nB| + rho * D + Efloor < MB i := by
  rcases hsmall Efloor hEfloor_pos with ⟨i, hMB_pos, hMB_le_floor⟩
  refine ⟨i, hMB_pos, ?_⟩
  intro A D nB rho hrho hD_nonneg
  exact residual_margin_impossible_of_error_floor_ge_margin
    hrho hD_nonneg hMB_le_floor

/-- Equivalent no-uniform-certificate form of
`exists_margin_index_impossible_of_arbitrarily_small_margins`: with a fixed
positive non-adaptive floor and arbitrarily small positive margins, it is
impossible that every margin index admits some quadratic residual certificate
with strict margin. -/
theorem not_forall_residual_margin_of_arbitrarily_small_margins
    {ι : Type} {MB : ι → ℝ} {Efloor : ℝ}
    (hEfloor_pos : 0 < Efloor)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ i : ι, 0 < MB i ∧ MB i ≤ eps) :
    ¬ ∀ i : ι, ∃ A D nB rho : ℝ,
      0 ≤ rho ∧
      0 ≤ D ∧
      |rho * A + nB| + rho * D + Efloor < MB i := by
  intro hcert
  rcases exists_margin_index_impossible_of_arbitrarily_small_margins
      hEfloor_pos hsmall with ⟨i, _hMB_pos, hno⟩
  rcases hcert i with ⟨A, D, nB, rho, hrho, hD_nonneg, hmargin⟩
  exact (hno A D nB rho hrho hD_nonneg) hmargin

/-- Variable-floor version of the no-uniform-certificate theorem.  If each
packet has its own non-adaptive floor but all those floors are bounded below by
a fixed positive `E0`, then arbitrarily small positive margins still rule out a
strict quadratic residual certificate for every margin index. -/
theorem not_forall_residual_margin_of_uniform_floor_arbitrarily_small_margins
    {ι : Type} {MB Efloor : ι → ℝ} {E0 : ℝ}
    (hE0_pos : 0 < E0)
    (hfloor_lb : ∀ i : ι, E0 ≤ Efloor i)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ i : ι, 0 < MB i ∧ MB i ≤ eps) :
    ¬ ∀ i : ι, ∃ A D nB rho : ℝ,
      0 ≤ rho ∧
      0 ≤ D ∧
      |rho * A + nB| + rho * D + Efloor i < MB i := by
  intro hcert
  rcases hsmall E0 hE0_pos with ⟨i, _hMB_pos, hMB_le_E0⟩
  rcases hcert i with ⟨A, D, nB, rho, hrho, hD_nonneg, hmargin⟩
  have hMB_le_floor : MB i ≤ Efloor i := le_trans hMB_le_E0 (hfloor_lb i)
  exact residual_margin_impossible_of_error_floor_ge_margin
    hrho hD_nonneg hMB_le_floor hmargin

end BAH1Quadratic
end JensenLadder
