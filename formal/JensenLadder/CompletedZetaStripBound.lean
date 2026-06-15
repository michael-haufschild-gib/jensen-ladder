import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.MellinTransform

/-!
# Vertical-strip bound for the entire completed zeta `Λ₀ = completedRiemannZeta₀`

The entire completed Riemann zeta `completedRiemannZeta₀` (the pole-cancelled `Λ₀`, defined in
mathlib as `(hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`, i.e. the Mellin transform of the modified even
theta kernel) is **bounded on every vertical strip `{a ≤ Re s ≤ b}`, uniformly in `Im s`**.

The proof is elementary and avoids Phragmén–Lindelöf / complex Stirling entirely:

* `Λ₀ s = mellin f_modif (s/2) / 2`, where `f_modif` decays exponentially at both `0` and `∞`
  (it is the `f` of a `StrongFEPair`), so the Mellin integral converges **absolutely for all `s`**.
* For `t > 0`, `‖(t:ℂ) ^ (s-1)‖ = t ^ (Re s - 1)` is **independent of `Im s`**, hence
  `‖mellin f s‖ ≤ ∫ t in Ioi 0, t ^ (Re s - 1) * ‖f t‖`, a quantity depending only on `Re s`.
* On a strip `a ≤ σ ≤ b` the pointwise bound `t ^ (σ/2-1) ≤ t ^ (a/2-1) + t ^ (b/2-1)`
  (valid for all `t > 0`) dominates the integrand by an integrable function independent of `σ`,
  giving a single uniform constant.

This is the strip-interior input to the order/zero-density program for `Ξ`: combined with the
off-strip `Γ`-growth bounds (`W1DensityNevanlinna`) and the functional equation it assembles the
disk order bound `M(r) ≤ exp(C r log r)` that feeds the Nevanlinna convergence-exponent estimate
`∑_ρ 1/(¼+γ²) < ∞`. **RH-agnostic; Theorem M does not prove RH by itself.**
-/

open MeasureTheory Complex Set HurwitzZeta

namespace CompletedZetaStripBound

/-- **Mellin modulus bound.** For `t > 0` the factor `‖(t:ℂ)^(s-1)‖ = t^(Re s - 1)` does not depend
on `Im s`, so the modulus of a Mellin transform is bounded by a real integral fixed by `Re s`. -/
theorem norm_mellin_le (f : ℝ → ℂ) (s : ℂ) :
    ‖mellin f s‖ ≤ ∫ t in Ioi (0:ℝ), t ^ (s.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

/-- The modulus of `completedRiemannZeta₀ s` is bounded by an integral depending only on `Re s`
(uniform in `Im s`), where `f_modif` is the modified even theta kernel of `hurwitzEvenFEPair 0`. -/
theorem norm_completedRiemannZeta₀_le (s : ℂ) :
    ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Ioi (0:ℝ), t ^ (s.re / 2 - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) / 2 := by
  have heq : completedRiemannZeta₀ s
      = (mellin ((hurwitzEvenFEPair 0).f_modif) (s / 2)) / 2 := rfl
  rw [heq, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hb : ‖mellin ((hurwitzEvenFEPair 0).f_modif) (s / 2)‖
      ≤ ∫ t in Ioi (0:ℝ), t ^ (s.re / 2 - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    refine (norm_mellin_le _ _).trans_eq ?_
    rw [show (s / 2).re = s.re / 2 from by simp]
  gcongr

/-- From Mellin convergence (absolute integrability of `(t:ℂ)^(s-1) • f t` on `Ioi 0`) we extract
integrability of the real dominating integrand `t ↦ t^(Re s - 1) * ‖f t‖`. -/
theorem integrableOn_rpow_mul_norm {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    IntegrableOn (fun t => t ^ (s.re - 1) * ‖f t‖) (Ioi 0) := by
  have hf' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi 0) := hf
  have hn : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • f t‖) (Ioi 0) := hf'.norm
  refine hn.congr_fun ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

/-- **Vertical-strip bound for the entire completed zeta.** `completedRiemannZeta₀` is bounded on
every vertical strip `{a ≤ Re s ≤ b}` by a single constant, uniformly in `Im s`. -/
theorem completedRiemannZeta₀_bounded_on_strip (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedRiemannZeta₀ s‖ ≤ C := by
  set g : ℝ → ℝ := fun t => ‖(hurwitzEvenFEPair 0).f_modif t‖ with hgdef
  have hconv : ∀ x : ℝ, MellinConvergent ((hurwitzEvenFEPair 0).f_modif) (x : ℂ) :=
    fun x => ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (x : ℂ)).1
  have hIa : IntegrableOn (fun t => t ^ (a / 2 - 1) * g t) (Ioi 0) := by
    have := integrableOn_rpow_mul_norm (hconv (a / 2)); simpa using this
  have hIb : IntegrableOn (fun t => t ^ (b / 2 - 1) * g t) (Ioi 0) := by
    have := integrableOn_rpow_mul_norm (hconv (b / 2)); simpa using this
  have hIab : IntegrableOn (fun t => (t ^ (a / 2 - 1) + t ^ (b / 2 - 1)) * g t) (Ioi 0) := by
    refine (hIa.add hIb).congr_fun ?_ measurableSet_Ioi
    intro t _; simp only [Pi.add_apply]; ring
  refine ⟨(∫ t in Ioi 0, (t ^ (a / 2 - 1) + t ^ (b / 2 - 1)) * g t) / 2, ?_⟩
  intro s ha hb'
  refine (norm_completedRiemannZeta₀_le s).trans ?_
  have hIs : IntegrableOn (fun t => t ^ (s.re / 2 - 1) * g t) (Ioi 0) := by
    have := integrableOn_rpow_mul_norm (hconv (s.re / 2)); simpa using this
  have hmono : (∫ t in Ioi 0, t ^ (s.re / 2 - 1) * g t)
      ≤ ∫ t in Ioi 0, (t ^ (a / 2 - 1) + t ^ (b / 2 - 1)) * g t := by
    refine setIntegral_mono_on hIs hIab measurableSet_Ioi (fun t ht => ?_)
    have htpos : (0:ℝ) < t := ht
    have hgnn : 0 ≤ g t := norm_nonneg _
    have hpow : t ^ (s.re / 2 - 1) ≤ t ^ (a / 2 - 1) + t ^ (b / 2 - 1) := by
      rcases le_total t 1 with hle | hge
      · have h1 : t ^ (s.re / 2 - 1) ≤ t ^ (a / 2 - 1) :=
          Real.rpow_le_rpow_of_exponent_ge htpos hle (by linarith)
        have h2 : (0:ℝ) ≤ t ^ (b / 2 - 1) := Real.rpow_nonneg htpos.le _
        linarith
      · have h1 : t ^ (s.re / 2 - 1) ≤ t ^ (b / 2 - 1) :=
          Real.rpow_le_rpow_of_exponent_le hge (by linarith)
        have h2 : (0:ℝ) ≤ t ^ (a / 2 - 1) := Real.rpow_nonneg htpos.le _
        linarith
    simpa using mul_le_mul_of_nonneg_right hpow hgnn
  linarith

/-- The **entire** ξ-numerator `s(s−1)Λ₀(s)` (`Λ₀ = completedRiemannZeta₀`) is polynomially bounded
(degree `2` in `‖s‖`) on every vertical strip. The transcendental factor `Λ₀` contributes a uniform
constant (the strip bound); all polynomial growth lives in the algebraic factor `s(s−1)`. This is the
strip-interior region of the disk order bound `M_Ξ(r) ≤ exp(C r log r)` for the carrier `Ξ`. -/
theorem norm_xiNum₀_le_on_strip (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ C * (‖s‖ + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := completedRiemannZeta₀_bounded_on_strip a b
  refine ⟨max C 0, le_max_right _ _, fun s ha hb => ?_⟩
  have hCs : ‖completedRiemannZeta₀ s‖ ≤ max C 0 := (hC s ha hb).trans (le_max_left _ _)
  have h1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by rw [norm_one]
  have h2 : ‖s‖ ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
  rw [norm_mul, norm_mul]
  calc ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
      ≤ (‖s‖ + 1) * (‖s‖ + 1) * max C 0 := by gcongr
    _ = max C 0 * (‖s‖ + 1) ^ 2 := by ring

/-- **Bridge between the two ξ-numerator representations.** Away from the poles `s = 0, 1` of
`completedRiemannZeta`, the meromorphic representation `s(s−1)·completedRiemannZeta s` (used for the
off-strip `Re s > 1` Dirichlet/`Γ`-growth bounds) equals the entire representation
`s(s−1)·completedRiemannZeta₀ s + 1` (used for the strip-interior bound). This lets the disk order
bound for the carrier `Ξ` be assembled from regional bounds in whichever representation is convenient. -/
theorem xiNum_completedRiemannZeta_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) * completedRiemannZeta s = s * (s - 1) * completedRiemannZeta₀ s + 1 := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun h => hs1 h.symm)
  rw [completedRiemannZeta_eq]
  field_simp
  ring

end CompletedZetaStripBound
