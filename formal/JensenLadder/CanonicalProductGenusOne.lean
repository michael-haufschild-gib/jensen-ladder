import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic

/-!
# Genus-one Weierstrass elementary factor estimate (reverse-bridge brick)

The reverse half of `GenusOneDeterminantControl` (zero-convergence ⟹ function-convergence)
needs locally-uniform convergence of genus-1 canonical products `∏ (1 − z/aₙ)·exp(z/aₙ)`.
mathlib already provides the product-convergence engine (`hasProdLocallyUniformlyOn_nat_one_add`,
given a summable majorant on compacts) and a worked genus-1 example (the Euler sine product in
`Analysis/SpecialFunctions/Trigonometric/Cotangent`). The missing ingredient for a *general*
zero set is the elementary-factor estimate proved here:

  `‖E₁(w) − 1‖ ≤ ‖w‖² · exp ‖w‖`,  where `E₁(w) = (1 − w)·exp w`.

This is the quadratic vanishing of the genus-1 factor at `0`, with an explicit constant. It is
the per-term bound that, with `Σ ‖aₙ‖⁻² < ∞`, feeds the mathlib product engine to give a locally
uniform (hence entire) canonical product. This brick does **not** discharge `hconv`; it is one
analytic ingredient of the open reverse bridge.

Evidence class: proved lemma / formal artifact. Theorem M is proven, but Theorem M does not prove
RH by itself.
-/

open Complex
open Metric Filter Topology

namespace JensenLadder.CanonicalProductGenusOne

/-- The genus-1 Weierstrass elementary factor `E₁(w) = (1 − w)·exp w`. -/
noncomputable def E1 (w : ℂ) : ℂ := (1 - w) * Complex.exp w

@[simp] lemma E1_zero : E1 0 = 1 := by simp [E1]

/-- `E₁'(w) = −w·exp w`. -/
lemma hasDerivAt_E1 (w : ℂ) : HasDerivAt E1 (-w * Complex.exp w) w := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)
  have h2 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
  have h := h1.mul h2
  convert h using 1
  ring

/-- The genus-1 elementary factor vanishes to second order at `0`, with an explicit constant:
`‖E₁(w) − 1‖ ≤ ‖w‖² · exp ‖w‖`. -/
lemma norm_E1_sub_one_le (w : ℂ) : ‖E1 w - 1‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
  -- Reduce to the real segment `t ↦ E₁(t • w)` on `[0,1]`.
  set F : ℝ → ℂ := fun t => E1 ((t : ℂ) * w) with hF
  have hFderiv : ∀ t : ℝ, HasDerivAt F (-((t : ℂ) * w) * Complex.exp ((t : ℂ) * w) * w) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt).mul_const w)
    simpa using (hasDerivAt_E1 ((t : ℂ) * w)).comp t hline
  -- Bound the derivative norm on `[0,1]`.
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖-((t : ℂ) * w) * Complex.exp ((t : ℂ) * w) * w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have htnorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
    have htw : ‖(t : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul]
      calc ‖(t : ℂ)‖ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
        _ = ‖w‖ := one_mul _
    have hre : ((t : ℂ) * w).re ≤ ‖w‖ :=
      le_trans (Complex.re_le_norm ((t : ℂ) * w)) htw
    have hnexp : ‖Complex.exp ((t : ℂ) * w)‖ = Real.exp (((t : ℂ) * w).re) := Complex.norm_exp _
    calc ‖-((t : ℂ) * w) * Complex.exp ((t : ℂ) * w) * w‖
        = ‖(t : ℂ) * w‖ * ‖Complex.exp ((t : ℂ) * w)‖ * ‖w‖ := by
          rw [norm_mul, norm_mul, norm_neg]
      _ ≤ ‖w‖ * Real.exp ‖w‖ * ‖w‖ := by
          rw [hnexp]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul htw (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (norm_nonneg _))
            (norm_nonneg _)
      _ = ‖w‖ ^ 2 * Real.exp ‖w‖ := by ring
  -- Mean value inequality on `[0,1]`.
  have hcont : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt F
      (-((t : ℂ) * w) * Complex.exp ((t : ℂ) * w) * w) (Set.Icc (0:ℝ) 1) t :=
    fun t _ => (hFderiv t).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont hbound (convex_Icc 0 1)
    (Set.right_mem_Icc.mpr zero_le_one) (Set.left_mem_Icc.mpr zero_le_one)
  -- `F 1 = E₁ w`, `F 0 = 1`, `‖1 - 0‖ = 1`.
  have hF1 : F 1 = E1 w := by simp [hF]
  have hF0 : F 0 = 1 := by simp [hF]
  rw [hF1, hF0] at hmvt
  calc
    ‖E1 w - 1‖ = dist (E1 w) 1 := by rw [dist_eq_norm]
    _ = dist 1 (E1 w) := dist_comm _ _
    _ = ‖1 - E1 w‖ := by rw [dist_eq_norm]
    _ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by simpa using hmvt

/-- The genus-1 factor estimate for a canonical-product zero at `a`. -/
lemma norm_E1_div_sub_one_le (z a : ℂ) :
    ‖E1 (z / a) - 1‖ ≤ (‖z‖ / ‖a‖) ^ 2 * Real.exp (‖z‖ / ‖a‖) := by
  simpa [norm_div] using norm_E1_sub_one_le (z / a)

/--
Uniform form of `norm_E1_div_sub_one_le` on a norm-bounded set.  This is the
per-factor estimate used before applying a locally-uniform product-convergence
theorem: on `‖z‖ ≤ R`, the `a`-th genus-one factor is controlled by the
compact majorant `(R / ‖a‖)^2 exp (R / ‖a‖)`.
-/
lemma norm_E1_div_sub_one_le_of_norm_le {z a : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hz : ‖z‖ ≤ R) :
    ‖E1 (z / a) - 1‖ ≤ (R / ‖a‖) ^ 2 * Real.exp (R / ‖a‖) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdiv : ‖z‖ / ‖a‖ ≤ R / ‖a‖ :=
    div_le_div_of_nonneg_right hz ha_pos.le
  have hdiv_nonneg : 0 ≤ ‖z‖ / ‖a‖ :=
    div_nonneg (norm_nonneg z) ha_pos.le
  have hsq :
      (‖z‖ / ‖a‖) ^ 2 ≤ (R / ‖a‖) ^ 2 :=
    pow_le_pow_left₀ hdiv_nonneg hdiv 2
  have hexp :
      Real.exp (‖z‖ / ‖a‖) ≤ Real.exp (R / ‖a‖) :=
    Real.exp_le_exp.mpr hdiv
  exact (norm_E1_div_sub_one_le z a).trans
    (mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _))

/--
If the zero `a` lies outside the radius-`R` disk, the compact factor estimate
has a fixed exponential constant.  This is the tail form needed for a
Weierstrass product majorant.
-/
lemma norm_E1_div_sub_one_le_of_norm_le_of_le_norm {z a : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hz : ‖z‖ ≤ R) (hRa : R ≤ ‖a‖) :
    ‖E1 (z / a) - 1‖ ≤ (R / ‖a‖) ^ 2 * Real.exp 1 := by
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdiv_le_one : R / ‖a‖ ≤ 1 := by
    rwa [div_le_one₀ ha_pos]
  have hexp : Real.exp (R / ‖a‖) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hdiv_le_one
  exact (norm_E1_div_sub_one_le_of_norm_le ha hz).trans
    (mul_le_mul_of_nonneg_left hexp (sq_nonneg _))

/--
The standard genus-one tail majorant is summable whenever the reciprocal-square
zero-height row is summable.
-/
lemma summable_genusOne_tail_majorant {a : ℕ → ℂ} {R : ℝ}
    (hsq : Summable (fun n : ℕ => (‖a n‖⁻¹) ^ 2)) :
    Summable (fun n : ℕ => (R / ‖a n‖) ^ 2 * Real.exp 1) := by
  refine (hsq.mul_left (R ^ 2 * Real.exp 1)).congr ?_
  intro n
  rw [div_eq_mul_inv]
  ring

/--
Eventually, once all zero heights are nonzero and outside the radius-`R` disk,
the genus-one factors are controlled by the summable tail majorant.
-/
lemma eventually_norm_E1_div_sub_one_le_tail_majorant {a : ℕ → ℂ} {R : ℝ}
    (htail : ∀ᶠ n in atTop, a n ≠ 0 ∧ R ≤ ‖a n‖) :
    ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖E1 (z / a n) - 1‖ ≤ (R / ‖a n‖) ^ 2 * Real.exp 1 := by
  filter_upwards [htail] with n hn z hz
  exact norm_E1_div_sub_one_le_of_norm_le_of_le_norm hn.1 hz hn.2

/--
Genus-one canonical products converge locally uniformly on a fixed disk once
the zero heights have summable reciprocal squares and eventually leave that
disk.

This is still only a product-convergence brick.  It does not identify the
product with a determinant, with `xiEntire`, or with any RH endpoint.
-/
lemma hasProdLocallyUniformlyOn_genusOneFactors_on_ball {a : ℕ → ℂ} {R : ℝ}
    (hsq : Summable (fun n : ℕ => (‖a n‖⁻¹) ^ 2))
    (htail : ∀ᶠ n in atTop, a n ≠ 0 ∧ R ≤ ‖a n‖) :
    HasProdLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => E1 (z / a n))
      (fun z : ℂ => ∏' n : ℕ, E1 (z / a n))
      (Metric.ball (0 : ℂ) R) := by
  let u : ℕ → ℝ := fun n => (R / ‖a n‖) ^ 2 * Real.exp 1
  have hu : Summable u := summable_genusOne_tail_majorant hsq
  have hbound : ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
      ‖E1 (z / a n) - 1‖ ≤ u n := by
    have htail_bound := eventually_norm_E1_div_sub_one_le_tail_majorant htail
    filter_upwards [htail_bound] with n hn z hzball
    have hz : ‖z‖ ≤ R := by
      rw [mem_ball_zero_iff] at hzball
      exact hzball.le
    exact hn z hz
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ => E1 (z / a n) - 1)
      (Metric.ball (0 : ℂ) R) := by
    intro n
    unfold E1
    fun_prop
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add (R := ℂ)
    isOpen_ball hu hbound hcts
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hprod

open Filter Topology in
/-- **Genus-1 canonical product converges locally uniformly.** For a zero set `aₙ ≠ 0` with
`Σ ‖aₙ‖⁻² < ∞`, the product `∏ₙ E₁(z/aₙ)` converges locally uniformly on `ℂ`. -/
lemma hasProdLocallyUniformlyOn_canonicalProduct
    {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hsum : Summable (fun n => ‖a n‖⁻¹ ^ 2)) :
    HasProdLocallyUniformlyOn (fun n z => E1 (z / a n))
      (fun z => ∏' n, E1 (z / a n)) Set.univ := by
  -- eventually `‖aₙ‖ ≥ 1` (since `‖aₙ‖⁻²  → 0`).
  have hge1 : ∀ᶠ n in cofinite, (1 : ℝ) ≤ ‖a n‖ := by
    have h0 := hsum.tendsto_cofinite_zero
    filter_upwards [h0.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with n hn
    have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
    have hid : ‖a n‖⁻¹ ^ 2 * ‖a n‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hpos), one_pow]
    nlinarith [hn, hpos, hid, mul_pos hpos hpos, sq_nonneg (‖a n‖ - 1)]
  -- reduce `E₁(z/aₙ) = 1 + (E₁(z/aₙ) − 1)` and apply the per-compact product engine.
  have key : HasProdLocallyUniformlyOn (fun n z => 1 + (E1 (z / a n) - 1))
      (fun z => ∏' n, (1 + (E1 (z / a n) - 1))) Set.univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set Rp : ℝ := max R 0 with hRp
    have hRp0 : 0 ≤ Rp := le_max_right _ _
    have hKRnorm : ∀ z ∈ K, ‖z‖ ≤ Rp := by
      intro z hz
      have hzc := hKR hz
      rw [Metric.mem_closedBall, dist_zero_right] at hzc
      exact hzc.trans (le_max_left _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      (u := fun n => Rp ^ 2 * Real.exp Rp * ‖a n‖⁻¹ ^ 2) (hsum.mul_left _) ?_ ?_
    · filter_upwards [hge1] with n hn z hz
      have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha n)
      have hb := norm_E1_div_sub_one_le_of_norm_le (z := z) (a := a n) (ha n) (hKRnorm z hz)
      refine hb.trans ?_
      have hdivle : Rp / ‖a n‖ ≤ Rp := by
        rw [div_le_iff₀ hpos]; nlinarith [hn, hRp0]
      calc (Rp / ‖a n‖) ^ 2 * Real.exp (Rp / ‖a n‖)
          ≤ (Rp / ‖a n‖) ^ 2 * Real.exp Rp := by gcongr
        _ = Rp ^ 2 * Real.exp Rp * ‖a n‖⁻¹ ^ 2 := by rw [div_pow]; ring
    · intro n
      exact Continuous.continuousOn (by unfold E1; fun_prop)
  -- transport `key` along `1 + (E₁ − 1) = E₁`.
  have he : (fun n z => 1 + (E1 (z / a n) - 1)) = fun n z => E1 (z / a n) := by
    funext n z; ring
  have he2 : (fun z => ∏' n, (1 + (E1 (z / a n) - 1))) = fun z => ∏' n, E1 (z / a n) := by
    funext z; congr 1; funext n; ring
  rw [he, he2] at key
  exact key
