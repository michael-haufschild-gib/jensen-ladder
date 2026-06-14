import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import JensenLadder.CauchyTransfer

/-!
# SD-C4 → SD-C5 moment-log-error bridge

This file closes the *magnitude* half of the SD-C5 log-branch obligation in
`docs/rh/sd_contour_legality_certificate.md` and assembles the cumulant-error
budget on top of the SD-C5 Cauchy core (`JensenLadder.CauchyTransfer`).

The SD-C4 step (`JensenLadder.LogTransfer`) shows the true moment is a controlled
multiplicative perturbation of the certificate: `w = z·(1+ε)`, `‖ε‖ ≤ τ/μ < 1`.
To feed SD-C5 we need a bound on the boundary log-error `‖log (Mt/Mc)‖`. Working
with the principal log of the **ratio** `Mt/Mc` (rather than `log Mt − log Mc`)
sidesteps the `log_mul` branch split: `Mt/Mc = 1 + ε` lies in `ball 1 1 ⊆`
slit plane, so `log (Mt/Mc) = log (1+ε)` and `mathlib`'s `Complex.norm_log_one_add_le`
applies.

`cumulant_error_bound_of_close` is the SD-C3→C4→C5 capstone: per-`k` connector
closeness on the boundary sphere plus the certificate floor `μ` and holomorphy
of the ratio-log on the closed `k`-disk give the explicit cumulant-error budget
`j! · η / ρ^j` with `η = (τ/μ)²/(2(1−τ/μ)) + τ/μ`.

## Honest scope

The branch *holomorphy* `DiffContOnCl ℂ (log (Mt/Mc)) (ball center ρ)` remains a
hypothesis — it is the SD analyticity-in-`k` input (`Mt`, `Mc` holomorphic in `k`,
ratio in the slit plane), the "holomorphy of the selected log branches" the
certificate flags. What is now formal is the *magnitude* bound that supplies `η`.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

open Complex Metric

namespace JensenLadder
namespace MomentLogError

/-- **SD-C5 boundary log-error magnitude.**
The principal log of the moment ratio `w/z` is bounded by an explicit function of
`τ/μ`: if `‖w − z‖ ≤ τ`, `μ ≤ ‖z‖`, and `τ < μ`, then
`‖log (w/z)‖ ≤ (τ/μ)²·(1−τ/μ)⁻¹/2 + τ/μ`. -/
theorem logRatio_norm_le {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau) (hmu : mu ≤ ‖z‖) (htau : tau < mu) :
    ‖Complex.log (w / z)‖ ≤ (tau / mu) ^ 2 * (1 - tau / mu)⁻¹ / 2 + tau / mu := by
  have htau0 : 0 ≤ tau := (norm_nonneg _).trans hclose
  have hmu0 : 0 < mu := htau0.trans_lt htau
  have hznorm : 0 < ‖z‖ := hmu0.trans_le hmu
  have hz : z ≠ 0 := norm_pos_iff.mp hznorm
  have hwz : w / z = 1 + (w - z) / z := by field_simp; ring
  have hεle : ‖(w - z) / z‖ ≤ tau / mu := by
    rw [norm_div]; exact div_le_div₀ htau0 hclose hmu0 hmu
  have hlt1 : tau / mu < 1 := (div_lt_one hmu0).mpr htau
  have hεlt : ‖(w - z) / z‖ < 1 := lt_of_le_of_lt hεle hlt1
  have hpos : 0 < 1 - tau / mu := by linarith
  rw [hwz]
  refine (Complex.norm_log_one_add_le hεlt).trans ?_
  gcongr

/-- **SD-C5 cumulant transfer via the moment-ratio log.**
Holomorphy of the ratio-log on the closed `k`-disk plus a boundary bound `η`
gives the `j`-th cumulant-error bound `j!·η/ρ^j`. (Re-exposes the Cauchy core in
the moment-ratio form, avoiding a `log_mul` branch split.) -/
theorem cumulant_error_bound
    {Mt Mc : ℂ → ℂ} {center : ℂ} {rho eta : ℝ} (j : ℕ)
    (hrho : 0 < rho)
    (hF : DiffContOnCl ℂ (fun k => Complex.log (Mt k / Mc k)) (ball center rho))
    (hη : ∀ k ∈ sphere center rho, ‖Complex.log (Mt k / Mc k)‖ ≤ eta) :
    ‖iteratedDeriv j (fun k => Complex.log (Mt k / Mc k)) center‖
      ≤ j.factorial * eta / rho ^ j :=
  CauchyTransfer.iteratedDeriv_norm_le_of_boundary_norm_le j hrho hF hη

/-- **SD-C3 → SD-C4 → SD-C5 capstone.**
Per-`k` connector closeness `‖Mt − Mc‖ ≤ τ` on the boundary sphere, the
certificate floor `μ ≤ ‖Mc‖`, the margin `τ < μ`, and holomorphy of the ratio-log
on the closed `k`-disk give the cumulant-error budget with the explicit `η`. -/
theorem cumulant_error_bound_of_close
    {Mt Mc : ℂ → ℂ} {center : ℂ} {rho tau mu : ℝ} (j : ℕ)
    (hrho : 0 < rho)
    (hF : DiffContOnCl ℂ (fun k => Complex.log (Mt k / Mc k)) (ball center rho))
    (hclose : ∀ k ∈ sphere center rho, ‖Mt k - Mc k‖ ≤ tau)
    (hmu : ∀ k ∈ sphere center rho, mu ≤ ‖Mc k‖)
    (htau : tau < mu) :
    ‖iteratedDeriv j (fun k => Complex.log (Mt k / Mc k)) center‖
      ≤ j.factorial * ((tau / mu) ^ 2 * (1 - tau / mu)⁻¹ / 2 + tau / mu) / rho ^ j :=
  cumulant_error_bound j hrho hF
    (fun k hk => logRatio_norm_le (hclose k hk) (hmu k hk) htau)

end MomentLogError
end JensenLadder
