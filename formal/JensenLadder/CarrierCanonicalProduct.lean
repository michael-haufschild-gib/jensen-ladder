import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The genus-0 carrier canonical product

For an absolutely summable family `a : ι → ℂ` of inverse eigenvalues (`a i = 1/u_ρ`, `u_ρ = ρ(1-ρ)`
in the squared variable, with `Σ |1/u_ρ| < ∞`), the carrier canonical product

  `P(w) = ∏' i, (1 - w * a i)`

is well-defined, converges locally uniformly on every ball, and is **entire**. The squared variable
puts the product at **genus 0** (`Σ |a i| < ∞`), so no Weierstrass/Hadamard exponential prefactor is
needed — the bare product is the object. This is the analytic backbone the spectral-pollution capstone
`riemannHypothesis_of_realRooted_locallyUniform_limit` consumes (it requires a locally-uniform limit of
holomorphic approximants); it carries no Schatten-class or metric hypothesis.

These are unconditional analytic facts about a summable eigenvalue family. They do **not** assert the
operator/identity `P = ξ/ξ(0)` (that is the open carrier construction) and do **not** prove RH;
Theorem M does not prove RH by itself.
-/

open Filter Function Complex Topology

namespace CarrierCanonicalProduct

/-- Genus-0 carrier factors are multipliable for each fixed `w`, from absolute summability of the
inverse eigenvalues `a i = 1/u_ρ`. -/
theorem multipliable_carrier {ι : Type*} (a : ι → ℂ) (ha : Summable a) (w : ℂ) :
    Multipliable (fun i => 1 - w * a i) := by
  have h : Summable (fun i => -(w * a i)) := (ha.mul_left w).neg
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable h

/-- The carrier canonical product `∏ (1 - w·a i)` converges locally uniformly on every ball, from the
genus-0 input `Σ ‖a i‖ < ∞`. -/
theorem hasProdLocallyUniformlyOn_carrier {ι : Type*}
    (a : ι → ℂ) (ha : Summable (fun i => ‖a i‖)) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun i (w : ℂ) => 1 - w * a i)
      (fun w => ∏' i, (1 - w * a i)) (Metric.ball (0 : ℂ) R) := by
  have hO : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hu : Summable (fun i => R * ‖a i‖) := ha.mul_left R
  have hbound : ∀ᶠ i in cofinite, ∀ w ∈ Metric.ball (0 : ℂ) R, ‖-(w * a i)‖ ≤ R * ‖a i‖ := by
    refine Filter.Eventually.of_forall (fun i w hw => ?_)
    rw [norm_neg, norm_mul]
    have hwR : ‖w‖ ≤ R := by
      have := Metric.mem_ball.mp hw; simpa [Complex.dist_eq] using this.le
    exact mul_le_mul_of_nonneg_right hwR (norm_nonneg _)
  have hcts : ∀ i, ContinuousOn (fun w : ℂ => -(w * a i)) (Metric.ball (0 : ℂ) R) := by
    intro i; fun_prop
  simpa only [sub_eq_add_neg] using
    Summable.hasProdLocallyUniformlyOn_one_add hO hu hbound hcts

/-- The carrier canonical product is holomorphic on every ball. -/
theorem differentiableOn_carrier (a : ℕ → ℂ) (ha : Summable (fun i => ‖a i‖)) (R : ℝ) :
    DifferentiableOn ℂ (fun w => ∏' i, (1 - w * a i)) (Metric.ball (0 : ℂ) R) := by
  have htlu := (hasProdLocallyUniformlyOn_carrier a ha R).tendstoLocallyUniformlyOn_finsetRange
  refine htlu.differentiableOn ?_ Metric.isOpen_ball
  refine Filter.Eventually.of_forall (fun n => ?_)
  have hfun : (fun b : ℂ => ∏ i ∈ Finset.range n, (1 - b * a i))
      = ∏ i ∈ Finset.range n, (fun b : ℂ => 1 - b * a i) := by
    ext b; simp [Finset.prod_apply]
  rw [hfun]
  exact DifferentiableOn.finsetProd (fun i _ => by fun_prop)

/-- **The genus-0 carrier canonical product `∏ (1 - w·a i)` is entire**, built purely from absolute
summability of `{a i = 1/u_ρ}` — no Hadamard prefactor, no Schatten class, no metric. The
locally-uniform holomorphic-limit form the capstone consumes. -/
theorem differentiable_carrier (a : ℕ → ℂ) (ha : Summable (fun i => ‖a i‖)) :
    Differentiable ℂ (fun w => ∏' i, (1 - w * a i)) := by
  intro w
  have hR : w ∈ Metric.ball (0 : ℂ) (‖w‖ + 1) := by
    simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]; linarith [norm_nonneg w]
  exact (differentiableOn_carrier a ha (‖w‖ + 1)).differentiableAt
          (Metric.isOpen_ball.mem_nhds hR)

/-- **Spectral correspondence:** the carrier canonical product vanishes at `w` iff some factor does,
i.e. iff `w · a i = 1` for some `i`. For `a i = 1/u_ρ` this says the zeros of the carrier product are
exactly the spectrum `{u_ρ}`. A non-circular general fact about absolutely convergent products. -/
theorem carrier_tprod_eq_zero_iff {ι : Type*} (a : ι → ℂ) (ha : Summable (fun i => ‖a i‖)) (w : ℂ) :
    (∏' i, (1 - w * a i)) = 0 ↔ ∃ i, w * a i = 1 := by
  have hconv : (fun i => 1 - w * a i) = (fun i => 1 + -(w * a i)) := by funext i; ring
  have hg : Summable (fun i => ‖-(w * a i)‖) := by
    have : Summable (fun i => ‖w‖ * ‖a i‖) := ha.mul_left ‖w‖
    simpa [norm_neg, norm_mul] using this
  constructor
  · intro h
    by_contra hne
    have hfac : ∀ i, (1 : ℂ) + -(w * a i) ≠ 0 := by
      intro i hi
      rw [add_neg_eq_zero] at hi
      exact hne ⟨i, hi.symm⟩
    have hprod := tprod_one_add_ne_zero_of_summable hfac hg
    rw [hconv] at h
    exact hprod h
  · rintro ⟨i, hi⟩
    refine tprod_of_exists_eq_zero ⟨i, ?_⟩
    rw [hi]; ring

/-- **Continuity in the eigenvalues (the reverse det↔eigenvalue bridge, genus-0 small-data form).**
If an eigenvalue family `a x · → aL ·` along a filter `𝓕` under a uniform summable bound `b`, and the
data is small (`‖w·a x k‖ ≤ ½` for all `x,k` — for the carrier `a k = 1/u_ρ` this holds on a large ball
since `sup‖1/u_ρ‖ ≈ 0.005`), then the carrier products converge:
`∏'(1 − w·a x k) → ∏'(1 − w·aL k)`. Proof: `∏ = exp(∑ log)` (`cexp_tsum_eq_tprod`), the log-sums converge
by **Tannery's theorem** (`tendsto_tsum_of_dominated_convergence`) with bound `(3/2)‖w‖ b k` via
`norm_log_one_add_half_le_self` and `continuousAt_clog`, then `exp` is continuous. This discharges the
"continuity in the zeros" piece flagged as the remaining tractable ingredient of the reverse bridge
(zero-convergence ⟹ function-convergence). RH-agnostic. -/
theorem tendsto_carrier_of_tendsto_eigenvalues {ι α : Type*} {𝓕 : Filter α} [𝓕.NeBot]
    (a : α → ι → ℂ) (aL : ι → ℂ) (b : ι → ℝ) (hb : Summable b) (w : ℂ)
    (hba : ∀ x k, ‖a x k‖ ≤ b k) (hbaL : ∀ k, ‖aL k‖ ≤ b k)
    (hsm : ∀ x k, ‖w * a x k‖ ≤ 1 / 2) (hsmL : ∀ k, ‖w * aL k‖ ≤ 1 / 2)
    (hconv : ∀ k, Tendsto (fun x => a x k) 𝓕 (𝓝 (aL k))) :
    Tendsto (fun x => ∏' k, (1 - w * a x k)) 𝓕 (𝓝 (∏' k, (1 - w * aL k))) := by
  have hre : ∀ (u : ℂ), ‖w * u‖ ≤ 1 / 2 → (1 / 2 : ℝ) ≤ (1 - w * u).re := by
    intro u hu
    have : (w * u).re ≤ ‖w * u‖ := Complex.re_le_norm _
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hslit : ∀ (u : ℂ), ‖w * u‖ ≤ 1 / 2 → (1 - w * u) ∈ slitPlane :=
    fun u hu => Or.inl (by have := hre u hu; linarith)
  have hne : ∀ (u : ℂ), ‖w * u‖ ≤ 1 / 2 → (1 - w * u) ≠ 0 := by
    intro u hu h; have := hre u hu; rw [h] at this; simp at this; linarith
  have hlogb : ∀ (u : ℂ) (k : ι), ‖u‖ ≤ b k → ‖w * u‖ ≤ 1 / 2 →
      ‖log (1 - w * u)‖ ≤ (3 / 2) * ‖w‖ * b k := by
    intro u k hk hu
    have h1 : ‖log (1 + (-(w * u)))‖ ≤ (3 / 2) * ‖(-(w * u))‖ :=
      norm_log_one_add_half_le_self (by simpa using hu)
    have h2 : (1 : ℂ) - w * u = 1 + (-(w * u)) := by ring
    rw [h2]
    calc ‖log (1 + -(w * u))‖ ≤ (3 / 2) * ‖(-(w * u))‖ := h1
      _ = (3 / 2) * (‖w‖ * ‖u‖) := by rw [norm_neg, norm_mul]
      _ ≤ (3 / 2) * (‖w‖ * b k) := by gcongr
      _ = (3 / 2) * ‖w‖ * b k := by ring
  set bound : ι → ℝ := fun k => (3 / 2) * ‖w‖ * b k with hbound_def
  have hsum_bound : Summable bound := by
    simpa [hbound_def, mul_assoc] using (hb.mul_left ((3 / 2) * ‖w‖))
  have hsumlog : ∀ x, Summable (fun k => log (1 - w * a x k)) := fun x =>
    Summable.of_norm_bounded hsum_bound (fun k => hlogb (a x k) k (hba x k) (hsm x k))
  have hsumlogL : Summable (fun k => log (1 - w * aL k)) :=
    Summable.of_norm_bounded hsum_bound (fun k => hlogb (aL k) k (hbaL k) (hsmL k))
  have hprod : ∀ x, (∏' k, (1 - w * a x k)) = exp (∑' k, log (1 - w * a x k)) := fun x =>
    (cexp_tsum_eq_tprod (fun k => hne (a x k) (hsm x k)) (hsumlog x)).symm
  have hprodL : (∏' k, (1 - w * aL k)) = exp (∑' k, log (1 - w * aL k)) :=
    (cexp_tsum_eq_tprod (fun k => hne (aL k) (hsmL k)) hsumlogL).symm
  have htan : Tendsto (fun x => ∑' k, log (1 - w * a x k)) 𝓕
      (𝓝 (∑' k, log (1 - w * aL k))) := by
    apply tendsto_tsum_of_dominated_convergence hsum_bound
    · intro k
      have hc : Tendsto (fun x => 1 - w * a x k) 𝓕 (𝓝 (1 - w * aL k)) :=
        ((hconv k).const_mul w).const_sub 1
      exact ((continuousAt_clog (hslit (aL k) (hsmL k))).tendsto).comp hc
    · exact Eventually.of_forall (fun x k => hlogb (a x k) k (hba x k) (hsm x k))
  rw [hprodL]; simp only [hprod]
  exact (Complex.continuous_exp.tendsto _).comp htan

/-- **Continuity in the eigenvalues, off the small-data ball (any `w`).** Drops the global `‖w·a x k‖≤½`
hypothesis of `tendsto_carrier_of_tendsto_eigenvalues` by a head/tail split: choose `K` with
`‖w‖·b k ≤ ½` for `k≥K` (possible since `b k→0`), handle the finite head by `tendsto_finsetProd` and the
tail by the small-data lemma, and recombine via `HasProd.prod_range_mul` (the monoid-correct product split
— ℂ is not a multiplicative group, so the group lemma `prod_mul_tprod_nat_add` does not apply). This is the
genus-0 reverse det↔eigenvalue bridge in full: eigenvalue-convergence ⟹ carrier-product-convergence, with
no restriction on `w`. RH-agnostic. -/
theorem tendsto_carrier_of_tendsto_eigenvalues_offball {α : Type*} {𝓕 : Filter α} [𝓕.NeBot]
    (a : α → ℕ → ℂ) (aL : ℕ → ℂ) (b : ℕ → ℝ) (hb : Summable b) (w : ℂ)
    (hba : ∀ x k, ‖a x k‖ ≤ b k) (hbaL : ∀ k, ‖aL k‖ ≤ b k)
    (hconv : ∀ k, Tendsto (fun x => a x k) 𝓕 (𝓝 (aL k))) :
    Tendsto (fun x => ∏' k, (1 - w * a x k)) 𝓕 (𝓝 (∏' k, (1 - w * aL k))) := by
  have htend : Tendsto (fun k => ‖w‖ * b k) atTop (𝓝 0) := by
    simpa using hb.tendsto_atTop_zero.const_mul ‖w‖
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, ‖w‖ * b k ≤ 1 / 2 := by
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htend (1 / 2) (by norm_num)
    exact ⟨K, fun k hk => le_of_lt (lt_of_abs_lt (by simpa [Real.dist_eq] using hK k hk))⟩
  have hsm_tail : ∀ (g : ℕ → ℂ), (∀ k, ‖g k‖ ≤ b k) → ∀ j, ‖w * g (j + K)‖ ≤ 1 / 2 := by
    intro g hg j
    rw [norm_mul]
    exact le_trans (by gcongr; exact hg (j + K)) (hK (j + K) (Nat.le_add_left K j))
  have htail : Tendsto (fun x => ∏' j, (1 - w * a x (j + K))) 𝓕
      (𝓝 (∏' j, (1 - w * aL (j + K)))) :=
    tendsto_carrier_of_tendsto_eigenvalues (fun x j => a x (j + K)) (fun j => aL (j + K))
      (fun j => b (j + K)) (hb.comp_injective (add_left_injective K)) w
      (fun x j => hba x (j + K)) (fun j => hbaL (j + K))
      (fun x j => hsm_tail (a x) (hba x) j) (fun j => hsm_tail aL hbaL j)
      (fun j => hconv (j + K))
  have hhead : Tendsto (fun x => ∏ k ∈ Finset.range K, (1 - w * a x k)) 𝓕
      (𝓝 (∏ k ∈ Finset.range K, (1 - w * aL k))) := by
    apply tendsto_finsetProd
    intro k _; exact ((hconv k).const_mul w).const_sub 1
  have hsplit : ∀ x, (∏' k, (1 - w * a x k))
      = (∏ k ∈ Finset.range K, (1 - w * a x k)) * (∏' j, (1 - w * a x (j + K))) := by
    intro x
    have hms : Multipliable (fun j => 1 - w * a x (j + K)) :=
      multipliable_carrier (fun j => a x (j + K))
        ((Summable.of_norm_bounded hb (hba x)).comp_injective (add_left_injective K)) w
    exact (HasProd.prod_range_mul (f := fun m => 1 - w * a x m) (k := K) hms.hasProd).tprod_eq
  have hsplitL : (∏' k, (1 - w * aL k))
      = (∏ k ∈ Finset.range K, (1 - w * aL k)) * (∏' j, (1 - w * aL (j + K))) := by
    have hms : Multipliable (fun j => 1 - w * aL (j + K)) :=
      multipliable_carrier (fun j => aL (j + K))
        ((Summable.of_norm_bounded hb hbaL).comp_injective (add_left_injective K)) w
    exact (HasProd.prod_range_mul (f := fun m => 1 - w * aL m) (k := K) hms.hasProd).tprod_eq
  rw [show (fun x => ∏' k, (1 - w * a x k))
      = (fun x => (∏ k ∈ Finset.range K, (1 - w * a x k)) * (∏' j, (1 - w * a x (j + K))))
      from funext hsplit, hsplitL]
  exact hhead.mul htail

/-- **Reality bridge (carrier-product level):** if every inverse-eigenvalue `a i` is real, then every
zero of the carrier canonical product is real. Zeros sit at `w = (a i)⁻¹`, and a real `a i` has a real
reciprocal. This is the product-level analogue of `ChiralDiracSquare.im_eq_zero_of_sq_eq_eigenvalue`:
real spectrum ⟹ real-rooted carrier — exactly the capstone's real-rooted-approximant input condition.
RH-agnostic (the easy direction; the converse is the RH content). -/
theorem carrier_zeros_real_of_eigenvalues_real {ι : Type*}
    (a : ι → ℂ) (ha : Summable (fun i => ‖a i‖)) (hre : ∀ i, (a i).im = 0)
    (w : ℂ) (hw : (∏' i, (1 - w * a i)) = 0) : w.im = 0 := by
  obtain ⟨i, hi⟩ := (carrier_tprod_eq_zero_iff a ha w).mp hw
  have hai : a i ≠ 0 := by
    rintro h; rw [h, mul_zero] at hi; exact one_ne_zero hi.symm
  have hw_eq : w = (a i)⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff hai]; exact hi
  rw [hw_eq, Complex.inv_im, hre i]; simp

/-- Off-line detector (contrapositive): a non-real zero of the carrier forces a non-real eigenvalue. -/
theorem exists_eigenvalue_im_ne_zero_of_carrier_zero_im_ne_zero {ι : Type*}
    (a : ι → ℂ) (ha : Summable (fun i => ‖a i‖))
    (w : ℂ) (hw : (∏' i, (1 - w * a i)) = 0) (hwim : w.im ≠ 0) : ∃ i, (a i).im ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  exact hwim (carrier_zeros_real_of_eigenvalues_real a ha h w hw)

end CarrierCanonicalProduct
