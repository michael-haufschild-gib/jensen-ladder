import Mathlib
import JensenLadder.RHReduction
open Complex Metric Filter Topology

namespace JensenLadder.HurwitzBridge


theorem logDeriv_sub_const_pow {z₀ : ℂ} (z : ℂ) (hz : z - z₀ ≠ 0) (n : ℕ) :
    logDeriv (fun w => (w - z₀) ^ n) z = (n : ℂ) / (z - z₀) := by
  have hd : HasDerivAt (fun w : ℂ => (w - z₀) ^ n) ((n : ℂ) * (z - z₀) ^ (n - 1)) z := by
    simpa using ((hasDerivAt_id z).sub_const z₀).pow n
  rw [logDeriv_apply, hd.deriv]
  rcases n with _ | m
  · simp
  · have h2 : (z - z₀) ^ m ≠ 0 := pow_ne_zero m hz
    simp only [Nat.add_sub_cancel, pow_succ]; field_simp

theorem subLemma1 {F : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsub : closedBall c R ⊆ U) (hFa : AnalyticOnNhd ℂ F U) (hFne : ∀ z ∈ U, F z ≠ 0) :
    (∮ z in C(c, R), logDeriv F z) = 0 := by
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR (s := (∅ : Set ℂ)) Set.countable_empty
  · have hderiv : AnalyticOnNhd ℂ (deriv F) U := hFa.deriv
    have : ContinuousOn (fun z => deriv F z / F z) (closedBall c R) :=
      ContinuousOn.div ((hderiv.continuousOn).mono hsub) ((hFa.continuousOn).mono hsub)
        (fun z hz => hFne z (hsub hz))
    simpa [logDeriv] using this
  · intro z hz
    have hzU : z ∈ U := hsub (ball_subset_closedBall hz.1)
    have hderiv : AnalyticOnNhd ℂ (deriv F) U := hFa.deriv
    simpa [logDeriv] using (hderiv z hzU).differentiableAt.div (hFa z hzU).differentiableAt (hFne z hzU)

theorem subLemma2 {h : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {R : ℝ} (hR0 : 0 < R)
    (hsub : closedBall z₀ R ⊆ U) (hh : AnalyticOnNhd ℂ h U) (hhne : ∀ z ∈ U, h z ≠ 0) (n : ℕ) :
    (∮ z in C(z₀, R), logDeriv (fun w => (w - z₀) ^ n * h w) z) = 2 * (Real.pi : ℂ) * I * (n : ℂ) := by
  have hmem : ∀ θ : ℝ, circleMap z₀ R θ ∈ U := fun θ =>
    hsub (sphere_subset_closedBall (circleMap_mem_sphere z₀ hR0.le θ))
  have hne : ∀ θ : ℝ, circleMap z₀ R θ - z₀ ≠ 0 := by
    intro θ; rw [circleMap_sub_center]; exact circleMap_ne_center (ne_of_gt hR0)
  have key : (∮ z in C(z₀, R), logDeriv (fun w => (w - z₀) ^ n * h w) z)
           = ∮ z in C(z₀, R), ((n : ℂ) / (z - z₀) + logDeriv h z) := by
    rw [circleIntegral, circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz : circleMap z₀ R θ - z₀ ≠ 0 := hne θ
    have hzU : circleMap z₀ R θ ∈ U := hmem θ
    have hpow : (circleMap z₀ R θ - z₀) ^ n ≠ 0 := pow_ne_zero n hz
    have hlm : logDeriv (fun w => (w - z₀) ^ n * h w) (circleMap z₀ R θ)
             = logDeriv (fun w => (w - z₀) ^ n) (circleMap z₀ R θ) + logDeriv h (circleMap z₀ R θ) := by
      refine logDeriv_mul (circleMap z₀ R θ) hpow (hhne _ hzU) ?_ ?_
      · exact (((hasDerivAt_id _).sub_const z₀).pow n).differentiableAt
      · exact (hh _ hzU).differentiableAt
    simp only [hlm, logDeriv_sub_const_pow _ hz n]
  rw [key, circleIntegral.integral_add]
  · have e1 : (fun z => (n : ℂ) / (z - z₀)) = (fun z => (n : ℂ) * (z - z₀)⁻¹) := by
      funext z; rw [div_eq_mul_inv]
    rw [e1, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR0),
        subLemma1 hR0.le hsub hh hhne]
    ring
  · have hz₀ : z₀ ∉ sphere z₀ |R| := by
      rw [Metric.mem_sphere, dist_self, abs_of_pos hR0]; exact fun heq => hR0.ne' heq.symm
    have hinv : CircleIntegrable (fun z => (z - z₀)⁻¹) z₀ R := circleIntegrable_sub_inv_iff.mpr (Or.inr hz₀)
    have : (fun z => (n : ℂ) / (z - z₀)) = (fun z => (n : ℂ) * (z - z₀)⁻¹) := by funext z; rw [div_eq_mul_inv]
    rw [this]; exact hinv.const_mul (n : ℂ)
  · apply ContinuousOn.circleIntegrable hR0.le
    have hderiv : AnalyticOnNhd ℂ (deriv h) U := hh.deriv
    exact ContinuousOn.div ((hderiv.continuousOn).mono (sphere_subset_closedBall.trans hsub))
      ((hh.continuousOn).mono (sphere_subset_closedBall.trans hsub))
      (fun z hz => hhne z ((sphere_subset_closedBall.trans hsub) hz))

-- VERIFIED (exit 0): ℂ uniform continuity of inv away from 0 (mathlib has only the ℝ version).
-- Unblocks sub-lemma 3's uniform-quotient route.
lemma uniformContinuousOn_inv_cpx {r : ℝ} (hr : 0 < r) :
    UniformContinuousOn (fun z : ℂ => z⁻¹) {z : ℂ | r ≤ ‖z‖} := by
  have hK : LipschitzOnWith (⟨(r ^ 2)⁻¹, by positivity⟩ : NNReal) (fun z : ℂ => z⁻¹) {z : ℂ | r ≤ ‖z‖} := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; linarith
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb; linarith
    have hna : (0:ℝ) < ‖a‖ := lt_of_lt_of_le hr ha
    have hnb : (0:ℝ) < ‖b‖ := lt_of_lt_of_le hr hb
    rw [dist_eq_norm, dist_eq_norm]
    have key : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
    rw [key, norm_div, norm_mul, norm_sub_rev b a]
    have hge : r ^ 2 ≤ ‖a‖ * ‖b‖ := by
      have := mul_le_mul ha hb (le_of_lt hr) (norm_nonneg a)
      simpa [pow_two] using this
    change ‖a - b‖ / (‖a‖ * ‖b‖) ≤ (r ^ 2)⁻¹ * ‖a - b‖
    rw [div_eq_mul_inv, mul_comm]; gcongr
  exact hK.uniformContinuousOn

-- VERIFIED (exit 0): pointwise logDeriv-difference bound — the analytic heart of sub-lemma 3.
-- ‖a/b - c/d‖ ≤ (2/m)‖a-c‖ + (2M/m²)‖d-b‖ when ‖b‖≥m/2, ‖d‖≥m, ‖c‖≤M.
-- With this, uniform logDeriv convergence follows from uniform deriv + uniform F convergence.
lemma logDeriv_dist_bound {a b c d : ℂ} {m M : ℝ} (hm : 0 < m)
    (hb : m/2 ≤ ‖b‖) (hd : m ≤ ‖d‖) (hc : ‖c‖ ≤ M) (hM : 0 ≤ M) :
    ‖a / b - c / d‖ ≤ (2/m) * ‖a - c‖ + (2*M/m^2) * ‖d - b‖ := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb; linarith
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd; linarith
  have hbpos : (0:ℝ) < ‖b‖ := lt_of_lt_of_le (by linarith) hb
  have hdpos : (0:ℝ) < ‖d‖ := lt_of_lt_of_le hm hd
  have key : a / b - c / d = (a - c) / b + c * (d - b) / (b * d) := by field_simp; ring
  rw [key]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_div, norm_div, norm_mul, norm_mul]
  gcongr
  · rw [div_le_iff₀ hbpos]
    calc ‖a - c‖ = (2/m)*‖a-c‖*(m/2) := by field_simp
      _ ≤ (2/m) * ‖a-c‖ * ‖b‖ := by gcongr
  · rw [div_le_iff₀ (by positivity)]
    calc ‖c‖ * ‖d - b‖ ≤ M * ‖d - b‖ := by gcongr
      _ = (2*M/m^2) * ‖d-b‖ * (m^2/2) := by field_simp
      _ ≤ (2*M/m^2) * ‖d-b‖ * (‖b‖*‖d‖) := by
          gcongr; calc m^2/2 = (m/2)*m := by ring
            _ ≤ ‖b‖ * ‖d‖ := by gcongr

-- VERIFIED (exit 0): brick #6 — uniform convergence of logDeriv from uniform deriv + uniform F.
-- (depends on logDeriv_dist_bound above). The analytic heart of sub-lemma 3.
lemma tendstoUniformlyOn_logDeriv {s : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M)
    (hd_ub : ∀ z ∈ s, ‖deriv g z‖ ≤ M) (hg_lb : ∀ z ∈ s, m ≤ ‖g z‖)
    (hF_lb : ∀ᶠ n in Filter.atTop, ∀ z ∈ s, m/2 ≤ ‖F n z‖)
    (hd : TendstoUniformlyOn (fun n => deriv (F n)) (deriv g) Filter.atTop s)
    (hf : TendstoUniformlyOn (fun n => F n) g Filter.atTop s) :
    TendstoUniformlyOn (fun n => logDeriv (F n)) (logDeriv g) Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hd hf ⊢
  intro ε hε
  have hδ1 : (0:ℝ) < ε * m / 4 := by positivity
  have hδ2 : (0:ℝ) < ε * m ^ 2 / (4 * (M + 1)) := by positivity
  filter_upwards [hd (ε * m / 4) hδ1, hf (ε * m ^ 2 / (4 * (M + 1))) hδ2, hF_lb] with n hdn hfn hFn
  intro z hz
  rw [dist_eq_norm, logDeriv_apply, logDeriv_apply, norm_sub_rev]
  have hbnd := logDeriv_dist_bound (a := deriv (F n) z) (b := F n z) (c := deriv g z) (d := g z)
    hm (hFn z hz) (hg_lb z hz) (hd_ub z hz) hM
  have e1 : ‖deriv (F n) z - deriv g z‖ < ε * m / 4 := by
    have h := hdn z hz; rw [dist_eq_norm, norm_sub_rev] at h; exact h
  have e2 : ‖g z - F n z‖ < ε * m ^ 2 / (4 * (M + 1)) := by
    have h := hfn z hz; rw [dist_eq_norm] at h; exact h
  have hbnd2 : (2/m) * ‖deriv (F n) z - deriv g z‖ + (2*M/m^2) * ‖g z - F n z‖ < ε := by
    have t1 : (2/m) * ‖deriv (F n) z - deriv g z‖ < (2/m) * (ε * m / 4) :=
      mul_lt_mul_of_pos_left e1 (by positivity)
    have t2 : (2*M/m^2) * ‖g z - F n z‖ ≤ (2*M/m^2) * (ε * m ^ 2 / (4 * (M + 1))) :=
      mul_le_mul_of_nonneg_left (le_of_lt e2) (by positivity)
    have b1 : (2/m) * (ε * m / 4) = ε / 2 := by field_simp; ring
    have b2 : (2*M/m^2) * (ε * m ^ 2 / (4 * (M + 1))) = M * ε / (2 * (M + 1)) := by field_simp; ring
    have b3 : M * ε / (2 * (M + 1)) ≤ ε / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hM, hε.le]
    nlinarith [t1, t2, b1, b2, b3]
  exact lt_of_le_of_lt hbnd hbnd2

-- VERIFIED (exit 0): brick #7 — factorization at an isolated zero.
-- g analytic at z₀, not locally 0 ⟹ ∃ n h r>0, h analytic+nonvanishing on ball z₀ r, g = (·-z₀)^n·h there.
-- Connects subLemma2 (argument principle) to a general g with an isolated zero.
open Metric Filter Topology in
lemma factor_isolated_zero {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (hgnz : ¬ ∀ᶠ z in 𝓝 z₀, g z = 0) :
    ∃ (n : ℕ) (h : ℂ → ℂ) (r : ℝ), 0 < r ∧ AnalyticOnNhd ℂ h (ball z₀ r) ∧
      (∀ z ∈ ball z₀ r, h z ≠ 0) ∧ (∀ z ∈ ball z₀ r, g z = (z - z₀) ^ n * h z) := by
  obtain ⟨n, h, hh_an, hh_ne, hfac⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hgnz
  obtain ⟨r1, hr1, hh_an_ball⟩ := hh_an.exists_ball_analyticOnNhd
  have hne_event : ∀ᶠ z in 𝓝 z₀, h z ≠ 0 := hh_an.continuousAt.eventually_ne hh_ne
  rw [eventually_nhds_iff_ball] at hne_event hfac
  obtain ⟨r2, hr2, hh_ne_ball⟩ := hne_event
  obtain ⟨r3, hr3, hfac_ball⟩ := hfac
  refine ⟨n, h, min r1 (min r2 r3), lt_min hr1 (lt_min hr2 hr3), ?_, ?_, ?_⟩
  · exact hh_an_ball.mono (ball_subset_ball (min_le_left _ _))
  · intro z hz
    exact hh_ne_ball z (ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hz)
  · intro z hz
    have := hfac_ball z (ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hz)
    rwa [smul_eq_mul] at this

-- VERIFIED (exit 0): brick #8 — sub-lemma 3 FULL (circle-integral convergence on a sphere where g≠0).
-- Composes brick #6 (uniform logDeriv) + compactness bounds + packaged tendsto_circleIntegral_of_continuousOn.
-- (depends on logDeriv_dist_bound, tendstoUniformlyOn_logDeriv above)
lemma tendsto_circleIntegral_logDeriv
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.sphere c R ⊆ U)
    (hga : AnalyticOnNhd ℂ g U) (hFa : ∀ n, AnalyticOnNhd ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F g Filter.atTop U)
    (hgne : ∀ z ∈ Metric.sphere c R, g z ≠ 0) :
    Filter.Tendsto (fun n => ∮ z in C(c,R), logDeriv (F n) z) Filter.atTop
      (nhds (∮ z in C(c,R), logDeriv g z)) := by
  have hSc : IsCompact (Metric.sphere c R) := isCompact_sphere c R
  have hSne : (Metric.sphere c R).Nonempty := ⟨circleMap c R 0, circleMap_mem_sphere c hR.le 0⟩
  have hf_unif : TendstoUniformlyOn F g Filter.atTop (Metric.sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hSc).mp (hconv.mono hsub)
  have hFdiff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (F n) U :=
    Filter.Eventually.of_forall (fun n => (hFa n).differentiableOn)
  have hd_unif : TendstoUniformlyOn (fun n => deriv (F n)) (deriv g) Filter.atTop (Metric.sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hSc).mp ((hconv.deriv hFdiff hU).mono hsub)
  obtain ⟨zm, hzm, hzmin⟩ := hSc.exists_isMinOn hSne
    (continuous_norm.comp_continuousOn ((hga.continuousOn).mono hsub))
  have hm_pos : 0 < ‖g zm‖ := norm_pos_iff.mpr (hgne zm hzm)
  have hg_lb : ∀ z ∈ Metric.sphere c R, ‖g zm‖ ≤ ‖g z‖ := isMinOn_iff.mp hzmin
  obtain ⟨zM, hzM, hzmax⟩ := hSc.exists_isMaxOn hSne
    (continuous_norm.comp_continuousOn ((hga.deriv.continuousOn).mono hsub))
  have hd_ub : ∀ z ∈ Metric.sphere c R, ‖deriv g z‖ ≤ ‖deriv g zM‖ := isMaxOn_iff.mp hzmax
  have hF_lb : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.sphere c R, ‖g zm‖/2 ≤ ‖F n z‖ := by
    rw [Metric.tendstoUniformlyOn_iff] at hf_unif
    filter_upwards [hf_unif (‖g zm‖/2) (by positivity)] with n hn z hz
    have h1 : dist (g z) (F n z) < ‖g zm‖/2 := hn z hz
    rw [dist_eq_norm] at h1
    have h3 : ‖g z‖ - ‖F n z‖ ≤ ‖g z - F n z‖ := norm_sub_norm_le _ _
    have h2 : ‖g zm‖ ≤ ‖g z‖ := hg_lb z hz
    linarith
  have hlog_unif : TendstoUniformlyOn (fun n => logDeriv (F n)) (logDeriv g) Filter.atTop (Metric.sphere c R) :=
    tendstoUniformlyOn_logDeriv hm_pos (norm_nonneg _) hd_ub hg_lb hF_lb hd_unif hf_unif
  have hcont : ∀ᶠ n in Filter.atTop, ContinuousOn (logDeriv (F n)) (Metric.sphere c R) := by
    filter_upwards [hF_lb] with n hn
    have hne : ∀ z ∈ Metric.sphere c R, F n z ≠ 0 := by
      intro z hz h0; have := hn z hz; rw [h0] at this; simp at this; linarith
    have : ContinuousOn (fun z => deriv (F n) z / F n z) (Metric.sphere c R) :=
      ContinuousOn.div (((hFa n).deriv.continuousOn).mono hsub) (((hFa n).continuousOn).mono hsub) hne
    simpa [logDeriv] using this
  exact hlog_unif.tendsto_circleIntegral_of_continuousOn hR.le hcont

open Metric Filter Topology in
lemma argprin_isolated {g h : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} {r : ℝ}
    {R : ℝ} (hR : 0 < R) (hRr : R < r)
    (hh_an : AnalyticOnNhd ℂ h (ball z₀ r)) (hh_ne : ∀ z ∈ ball z₀ r, h z ≠ 0)
    (hfac : ∀ z ∈ ball z₀ r, g z = (z - z₀) ^ n * h z) :
    (∮ z in C(z₀, R), logDeriv g z) = 2 * (Real.pi : ℂ) * I * (n : ℂ) := by
  have hsub : closedBall z₀ R ⊆ ball z₀ r := by
    intro z hz; rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hcong : (∮ z in C(z₀, R), logDeriv g z)
             = ∮ z in C(z₀, R), logDeriv (fun w => (w - z₀) ^ n * h w) z := by
    rw [circleIntegral, circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    have hmem : circleMap z₀ R θ ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]; exact hRr
    have hEv : g =ᶠ[𝓝 (circleMap z₀ R θ)] (fun w => (w - z₀) ^ n * h w) := by
      filter_upwards [isOpen_ball.mem_nhds hmem] with w hw using hfac w hw
    simp only [smul_eq_mul]
    rw [logDeriv_apply, logDeriv_apply, hEv.deriv_eq, hEv.eq_of_nhds]
  rw [hcong]
  exact subLemma2 hR hsub hh_an hh_ne n

open Metric Filter Topology in
lemma nowhere_zero_hurwitz {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hga : AnalyticOnNhd ℂ g U) (hFa : ∀ n, AnalyticOnNhd ℂ (F n) U)
    (hFne : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F g atTop U)
    (hg0 : ∃ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, g z ≠ 0 := by
  intro z₀ hz₀ hgz0
  have hgnz_local : ¬ ∀ᶠ z in 𝓝 z₀, g z = 0 := by
    intro hev
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 := (hev.filter_mono nhdsWithin_le_nhds).frequently
    have hEq : Set.EqOn g 0 U := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero hUconn hz₀ hfreq
    obtain ⟨w, hw, hgw⟩ := hg0; exact hgw (hEq hw)
  obtain ⟨n, h, r, hr, hh_an, hh_ne, hfac⟩ := factor_isolated_zero (hga z₀ hz₀) hgnz_local
  have hn1 : 1 ≤ n := by
    have hval : g z₀ = (z₀ - z₀) ^ n * h z₀ := hfac z₀ (mem_ball_self hr)
    rw [hgz0, sub_self] at hval
    rcases n with _ | m
    · exfalso; simp only [pow_zero, one_mul] at hval
      exact (hh_ne z₀ (mem_ball_self hr)) hval.symm
    · omega
  obtain ⟨rU, hrU, hrU_sub⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set R := min r rU / 2 with hRdef
  have hR : 0 < R := by have := lt_min hr hrU; positivity
  have hRr : R < r := by rw [hRdef]; have := min_le_left r rU; linarith
  have hRrU : R < rU := by rw [hRdef]; have := min_le_right r rU; linarith
  have hcb_ball : closedBall z₀ R ⊆ ball z₀ r := fun z hz => by
    rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hcb_U : closedBall z₀ R ⊆ U := fun z hz => by
    apply hrU_sub; rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hsph_ball : sphere z₀ R ⊆ ball z₀ r := fun z hz => hcb_ball (sphere_subset_closedBall hz)
  have hsph_U : sphere z₀ R ⊆ U := fun z hz => hcb_U (sphere_subset_closedBall hz)
  have hgne_sphere : ∀ z ∈ sphere z₀ R, g z ≠ 0 := by
    intro z hz
    rw [hfac z (hsph_ball hz)]
    have hz_ne : z - z₀ ≠ 0 := by
      rw [sub_ne_zero]; intro he; rw [he, mem_sphere, dist_self] at hz; linarith
    exact mul_ne_zero (pow_ne_zero n hz_ne) (hh_ne z (hsph_ball hz))
  have hint_g : (∮ z in C(z₀, R), logDeriv g z) = 2 * (Real.pi : ℂ) * I * (n : ℂ) :=
    argprin_isolated hR hRr hh_an hh_ne hfac
  have hint_F : (fun k => ∮ z in C(z₀, R), logDeriv (F k) z) = fun _ => (0 : ℂ) := by
    funext k; exact subLemma1 hR.le hcb_U (hFa k) (fun z hz => hFne k z hz)
  have htends := tendsto_circleIntegral_logDeriv hU hR hsph_U hga hFa hconv hgne_sphere
  rw [hint_g, hint_F] at htends
  have heq : (0 : ℂ) = 2 * (Real.pi : ℂ) * I * (n : ℂ) :=
    tendsto_nhds_unique tendsto_const_nhds htends
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnez : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hnez) heq.symm

open Metric Filter Topology in
/-- The Hurwitz real-rootedness transfer: a locally-uniform limit of entire,
only-real-zero approximants has only real zeros (given the limit ≢ 0). -/
theorem hurwitz_realRooted_transfer {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hFa : ∀ n, AnalyticOnNhd ℂ (F n) Set.univ)
    (hF_real : ∀ n z, F n z = 0 → z.im = 0)
    (hga : AnalyticOnNhd ℂ g Set.univ)
    (hconv : TendstoLocallyUniformlyOn F g atTop Set.univ)
    (hg0 : ∃ z, g z ≠ 0) :
    ∀ z, g z = 0 → z.im = 0 := by
  have key : ∀ (H : Set ℂ), IsOpen H → IsPreconnected H → H.Nonempty →
      (∀ z ∈ H, z.im ≠ 0) → ∀ z ∈ H, g z ≠ 0 := by
    intro H hHopen hHconn hHne hHim
    have hg0' : ∃ z ∈ H, g z ≠ 0 := by
      by_contra hcon; push Not at hcon
      obtain ⟨w, hgw⟩ := hg0; obtain ⟨p, hp⟩ := hHne
      have hev : ∀ᶠ z in 𝓝 p, g z = 0 := by
        filter_upwards [hHopen.mem_nhds hp] with z hz using hcon z hz
      have hfreq : ∃ᶠ z in 𝓝[≠] p, g z = 0 := (hev.filter_mono nhdsWithin_le_nhds).frequently
      exact hgw ((hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ p) hfreq) (Set.mem_univ w))
    exact nowhere_zero_hurwitz hHopen hHconn (hga.mono (Set.subset_univ H))
      (fun n => (hFa n).mono (Set.subset_univ H))
      (fun n z hz h0 => hHim z hz (hF_real n z h0))
      (hconv.mono (Set.subset_univ H)) hg0'
  intro z₀ hgz0
  by_contra hnonreal
  rcases lt_or_gt_of_ne hnonreal with hlt | hgt
  · have hpre : IsPreconnected {z : ℂ | z.im < 0} := by
      have he : {z : ℂ | z.im < 0} = Complex.imCLM.toLinearMap ⁻¹' (Set.Iio 0) := by
        ext z; simp [Set.mem_Iio]
      rw [he]; exact ((convex_Iio (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap).isPreconnected
    exact key {z : ℂ | z.im < 0} (isOpen_lt Complex.continuous_im continuous_const) hpre
      ⟨-Complex.I, by simp⟩ (fun z hz => ne_of_lt hz) z₀ hlt hgz0
  · have hpre : IsPreconnected {z : ℂ | 0 < z.im} := by
      have he : {z : ℂ | 0 < z.im} = Complex.imCLM.toLinearMap ⁻¹' (Set.Ioi 0) := by
        ext z; simp [Set.mem_Ioi]
      rw [he]; exact ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap).isPreconnected
    exact key {z : ℂ | 0 < z.im} (isOpen_lt continuous_const Complex.continuous_im) hpre
      ⟨Complex.I, by simp⟩ (fun z hz => ne_of_gt hz) z₀ hgt hgz0

noncomputable def xiEntire (z : ℂ) : ℂ :=
  (1/2) * ((1/2 + I * z) * (1/2 + I * z - 1) * completedRiemannZeta₀ (1/2 + I * z) + 1)

lemma xiEntire_differentiable : Differentiable ℂ xiEntire := by
  have hL : Differentiable ℂ (fun z : ℂ => completedRiemannZeta₀ (1/2 + I * z)) :=
    differentiable_completedZeta₀.comp (by fun_prop)
  unfold xiEntire
  fun_prop (disch := assumption)

lemma xi_pole_cancel (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s * (s - 1) * completedRiemannZeta s = s * (s - 1) * completedRiemannZeta₀ s + 1 := by
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := fun h => h1 (sub_eq_zero.mp h).symm
  field_simp
  ring



lemma completedRiemannZeta_one_ne_zero : completedRiemannZeta 1 ≠ 0 := by
  rw [completedRiemannZeta_one]
  have h4pi : (0:ℝ) ≤ 4 * Real.pi := by positivity
  have hcast : (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_log h4pi, ← Complex.ofReal_sub]
  have he : ((Real.eulerMascheroniConstant - Real.log (4 * Real.pi) : ℝ) : ℂ) / 2
       = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.ofReal_ne_zero]
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog : (1 : ℝ) < Real.log (4 * Real.pi) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) < 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    linarith
  intro h; have : Real.eulerMascheroniConstant = Real.log (4 * Real.pi) := by linarith
  linarith

lemma completedRiemannZeta_zero_ne_zero : completedRiemannZeta 0 ≠ 0 := by
  have h := completedRiemannZeta_one_sub 1
  rw [show (1:ℂ) - 1 = 0 by ring] at h
  rw [h]; exact completedRiemannZeta_one_ne_zero

lemma riemannXi_zero_imp_xiEntire_zero (z : ℂ)
    (hz : completedRiemannZeta (1/2 + I * z) = 0) : xiEntire z = 0 := by
  set s := (1/2 + I * z : ℂ) with hs
  have hs0 : s ≠ 0 := fun h => completedRiemannZeta_zero_ne_zero (h ▸ hz)
  have hs1 : s ≠ 1 := fun h => completedRiemannZeta_one_ne_zero (h ▸ hz)
  have hpc := xi_pole_cancel s hs0 hs1
  unfold xiEntire
  rw [← hs, hpc.symm, hz]; ring

lemma xiEntire_ne_zero : ∃ z, xiEntire z ≠ 0 := by
  refine ⟨I / 2, ?_⟩
  have hfac : (1 / 2 + I * (I / 2) : ℂ) = 0 := by
    rw [show I * (I / 2) = (I * I) / 2 from by ring, Complex.I_mul_I]; ring
  unfold xiEntire
  simp only [hfac, zero_sub, zero_mul, zero_add, mul_one]
  norm_num

theorem riemannHypothesis_of_realRooted_tendsto_xiEntire
    (F : ℕ → ℂ → ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (F n) Set.univ)
    (hF_real : ∀ n z, F n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn F xiEntire atTop Set.univ) :
    RiemannHypothesis := by
  have hga : AnalyticOnNhd ℂ xiEntire Set.univ :=
    (xiEntire_differentiable.differentiableOn).analyticOnNhd isOpen_univ
  have hXireal : ∀ z, xiEntire z = 0 → z.im = 0 :=
    hurwitz_realRooted_transfer hFa hF_real hga hconv xiEntire_ne_zero
  apply JensenLadder.RHReduction.riemannHypothesis_of_riemannXi_zeros_real
  intro z hz
  exact hXireal z (riemannXi_zero_imp_xiEntire_zero z hz)


end JensenLadder.HurwitzBridge
