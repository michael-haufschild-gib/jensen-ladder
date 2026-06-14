import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic log-transfer core

This file formalizes the algebraic part of the SD-C4/SD-C5 moment-transfer
gate.  If a certified contour value is bounded below by `mu` and the omitted
tail/connector error is at most `tau < mu`, then the true value is nonzero and
differs from the certificate by a multiplicative error of norm at most
`tau / mu < 1`.
-/

namespace JensenLadder
namespace LogTransfer

/--
Reverse triangle lower bound in certificate form.

If `z` is the certified value, `w` is the true value, `‖w - z‖ <= tau`, and
`mu <= ‖z‖`, then `‖w‖ >= mu - tau`.
-/
theorem norm_lower_of_close
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖) :
    mu - tau ≤ ‖w‖ := by
  have hdiff : ‖z‖ - ‖w‖ ≤ ‖w - z‖ := by
    calc
      ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
      _ = ‖w - z‖ := norm_sub_rev z w
  have hz_le : ‖z‖ ≤ tau + ‖w‖ := by
    linarith
  have hmu_le : mu ≤ tau + ‖w‖ := hmu.trans hz_le
  linarith

/--
Certified non-vanishing of the true value.
-/
theorem true_ne_zero_of_close
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖)
    (htau : tau < mu) :
    w ≠ 0 := by
  have hlower : mu - tau ≤ ‖w‖ := norm_lower_of_close hclose hmu
  have hpos : 0 < mu - tau := by linarith
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hpos hlower
  exact norm_pos_iff.mp hwpos

/--
Certified non-vanishing of the certified value.
-/
theorem cert_ne_zero_of_close
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖)
    (htau : tau < mu) :
    z ≠ 0 := by
  have htau_nonneg : 0 ≤ tau := (norm_nonneg (w - z)).trans hclose
  have hmu_pos : 0 < mu := lt_of_le_of_lt htau_nonneg htau
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hmu_pos hmu
  exact norm_pos_iff.mp hz_pos

/--
The additive error divided by the certified value is bounded by `tau / mu`.
-/
theorem relative_error_norm_le
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖)
    (htau : tau < mu) :
    ‖(w - z) / z‖ ≤ tau / mu := by
  have htau_nonneg : 0 ≤ tau := (norm_nonneg (w - z)).trans hclose
  have hmu_pos : 0 < mu := lt_of_le_of_lt htau_nonneg htau
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hmu_pos hmu
  calc
    ‖(w - z) / z‖ = ‖w - z‖ / ‖z‖ := by
      rw [Complex.norm_div]
    _ ≤ tau / ‖z‖ :=
      div_le_div_of_nonneg_right hclose (norm_nonneg z)
    _ ≤ tau / mu :=
      div_le_div_of_nonneg_left htau_nonneg hmu_pos hmu

/--
The relative error is strictly inside the unit disk.
-/
theorem relative_error_norm_lt_one
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖)
    (htau : tau < mu) :
    ‖(w - z) / z‖ < 1 := by
  have htau_nonneg : 0 ≤ tau := (norm_nonneg (w - z)).trans hclose
  have hmu_pos : 0 < mu := lt_of_le_of_lt htau_nonneg htau
  have hrel : ‖(w - z) / z‖ ≤ tau / mu :=
    relative_error_norm_le hclose hmu htau
  have hratio : tau / mu < 1 := (div_lt_one hmu_pos).mpr htau
  exact lt_of_le_of_lt hrel hratio

/--
The true value is the certified value times a controlled unit-disk
perturbation.
-/
theorem true_eq_cert_mul_one_plus_relative_error
    {z w : ℂ}
    (hz : z ≠ 0) :
    w = z * (1 + (w - z) / z) := by
  field_simp [hz]
  ring

/--
SD-C4 package: nonzero true value plus multiplicative perturbation with
`‖eps‖ <= tau/mu < 1`.
-/
theorem exists_relative_error
    {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau)
    (hmu : mu ≤ ‖z‖)
    (htau : tau < mu) :
    ∃ eps : ℂ,
      w = z * (1 + eps) ∧
      ‖eps‖ ≤ tau / mu ∧
      ‖eps‖ < 1 ∧
      w ≠ 0 := by
  let eps : ℂ := (w - z) / z
  have hz : z ≠ 0 := cert_ne_zero_of_close hclose hmu htau
  refine ⟨eps, true_eq_cert_mul_one_plus_relative_error hz, ?_, ?_, ?_⟩
  · exact relative_error_norm_le hclose hmu htau
  · exact relative_error_norm_lt_one hclose hmu htau
  · exact true_ne_zero_of_close hclose hmu htau

end LogTransfer
end JensenLadder
