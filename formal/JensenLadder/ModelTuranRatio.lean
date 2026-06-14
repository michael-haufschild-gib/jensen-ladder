import Mathlib

/-!
# Closed form for the Theorem-M model Turán ratios

Theorem M's critical-model coefficient sequence is `b k = M k / (2k)!`, where the
moments satisfy the (proven, `TheoremM.Defs.M_ratio`) identity
`M (k+1) = M k · (k + 1/2) · exp(γ − H_k)`.  Dividing by factorials, this is exactly
the consecutive-ratio recurrence

  `b (k+1) = b k · exp(γ − H_k) / (4 (k+1))`.

This file proves, **purely from that recurrence**, that the (raw, Toeplitz) Turán
ratio of the model coefficients has the closed form

  `b(k+1)² / (b k · b(k+2)) = (1 + 1/(k+1)) · exp(1/(k+1))`.

Hence the model's log-concavity margin is `σ_m − 1 ~ 2/m` (it `→ 1` at rate `2/m`).
This is a structural fact about the *model* (the Hermite/Laguerre-½ limit, cf. GORZ
2019); it is NOT about ξ and does NOT prove RH.  Working note:
`docs/rh/what_if_rabbit_holes_20260614.md` RH#17.

Author: Fable, 2026-06-14.  (New file; targeted build only.)
-/

namespace JensenLadder.ModelTuranRatio

open Real

/-- The harmonic difference, cast to `ℝ`: `H_{k+1} − H_k = 1/(k+1)`. -/
lemma harmonic_real_step (k : ℕ) :
    (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
  rw [harmonic_succ k]; push_cast; ring

/-- **Model Turán ratio (closed form).**  Any positive sequence `b` obeying the
Theorem-M consecutive-ratio recurrence has Turán ratio `(1 + 1/(k+1)) · exp(1/(k+1))`. -/
theorem model_turan_ratio
    (b : ℕ → ℝ) (hpos : ∀ k, 0 < b k)
    (hrat : ∀ k, b (k + 1)
        = b k * Real.exp (eulerMascheroniConstant - (harmonic k : ℝ)) / (4 * ((k : ℝ) + 1)))
    (k : ℕ) :
    b (k + 1) ^ 2 / (b k * b (k + 2))
      = (1 + 1 / ((k : ℝ) + 1)) * Real.exp (1 / ((k : ℝ) + 1)) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hbk : b k ≠ 0 := (hpos k).ne'
  have hbk1 : b (k + 1) ≠ 0 := (hpos (k + 1)).ne'
  have hA : Real.exp (eulerMascheroniConstant - (harmonic k : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hE : Real.exp (1 / ((k : ℝ) + 1)) ≠ 0 := (Real.exp_pos _).ne'
  -- expand the two recurrence steps
  have h1 : b (k + 1)
      = b k * Real.exp (eulerMascheroniConstant - (harmonic k : ℝ)) / (4 * ((k : ℝ) + 1)) := hrat k
  have h2 : b (k + 2)
      = b (k + 1) * Real.exp (eulerMascheroniConstant - (harmonic (k + 1) : ℝ)) / (4 * ((k : ℝ) + 2)) := by
    have e := hrat (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at e
    rw [e]; push_cast; ring
  -- exponent split: exp(γ - H_{k+1}) = exp(γ - H_k) / exp(1/(k+1))
  have hexp : Real.exp (eulerMascheroniConstant - (harmonic (k + 1) : ℝ))
      = Real.exp (eulerMascheroniConstant - (harmonic k : ℝ)) / Real.exp (1 / ((k : ℝ) + 1)) := by
    rw [← Real.exp_sub, harmonic_real_step k]; congr 1; ring
  -- algebra
  rw [h2, h1, hexp]
  field_simp
  ring
