import JensenLadder.W1DensityNevanlinna
import JensenLadder.CompletedZetaStripBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Order bound for the carrier `Ξ` — regional assembly (W1-density, brick 2/3)

Target: the disk order bound `M_Ξ(r) ≤ exp(C r log r)` for `Ξ(z) = ξ(½ + iz)`, the input to the
Nevanlinna convergence-exponent estimate `∑_ρ 1/(¼+γ²) < ∞` that discharges the carrier canonical
product's summability hypothesis. On the circle `|z| = r` (`s = ½ + iz`, `σ = Re s ∈ [½−r, ½+r]`) the
entire ξ-numerator `s(s−1)·completedRiemannZeta s = s(s−1)·completedRiemannZeta₀ s + 1` is bounded
region-by-region:

* **strip interior** `|σ − ½|` small — `CompletedZetaStripBound.norm_xiNum₀_le_on_strip`
  (`O(‖s‖²)`, via the Mellin uniform `Λ₀` strip bound);
* **right** `σ ≥ 4` — `norm_xiNum_le_offstrip` below (`‖s‖‖s−1‖ · ⌈σ/2⌉^⌈σ/2⌉ · Z₂`, the `Γ`-factor
  order-1 growth, `≤ exp(C σ log σ)`);
* **left** `σ < 0` — `W1DensityNevanlinna.norm_xiNumerator_le_of_re_lt` (FE transport of the right
  bound).

This file lands the **right-region** assembly (the `Γ`-growth bound in closed `⌈σ/2⌉^⌈σ/2⌉` form) plus
the Dirichlet-sum bound it needs. Bridge `xiNum_completedRiemannZeta_eq` (in `CompletedZetaStripBound`)
reconciles the two representations. **RH-agnostic; Theorem M does not prove RH by itself.**
-/

open Complex Real

namespace XiOrderBound

/-- The `Re>1` Dirichlet tail `∑ 1/(n+1)^σ` is monotone decreasing in `σ`, so on `σ ≥ 2` it is
bounded by the fixed constant `Z₂ = ∑ 1/(n+1)²`. -/
theorem dirichlet_sum_le {σ : ℝ} (hσ : 2 ≤ σ) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ) := by
  have hsumσ : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) := by
    have := (Real.summable_one_div_nat_add_rpow 1 σ).mpr (by linarith)
    refine this.congr (fun n => ?_); rw [abs_of_nonneg (by positivity)]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℝ)) := by
    have := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    refine this.congr (fun n => ?_); rw [abs_of_nonneg (by positivity)]
  refine Summable.tsum_le_tsum (fun n => ?_) hsumσ hsum2
  have hb : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_le_rpow_of_exponent_le hb hσ)

/-- **Off-strip (right) `Γ`-growth bound, `Re s ≥ 4`.** The entire ξ-numerator is bounded by
`‖s‖‖s−1‖ · ⌈σ/2⌉^⌈σ/2⌉ · Z₂` (`Z₂ = ∑ 1/(n+1)²`) — an `exp(C·σ log σ)`-type bound. Combines the
`Re>1` edge bound (`norm_xiNumerator_le`), `π^(−σ/2) ≤ 1`, the order-1 `Γ`-growth
`Γ(σ/2) ≤ ⌈σ/2⌉^⌈σ/2⌉` (`Gamma_le_ceil_pow`), and the Dirichlet bound above. This is the right-hand
region of the disk order bound; FE transports it to `Re s < 0` (`norm_xiNumerator_le_of_re_lt`). -/
theorem norm_xiNum_le_offstrip {s : ℂ} (hs : 4 ≤ s.re) :
    ‖s * (s - 1) * completedRiemannZeta s‖
      ≤ ‖s‖ * ‖s - 1‖ *
        (((⌈s.re / 2⌉₊ : ℝ) ^ (⌈s.re / 2⌉₊ : ℕ)) * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ))) := by
  refine (W1DensityNevanlinna.norm_xiNumerator_le (by linarith)).trans ?_
  have hΓnn : (0 : ℝ) ≤ Real.Gamma (s.re / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hπ1 : Real.pi ^ (-s.re / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
  have hX : Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2)
      ≤ (⌈s.re / 2⌉₊ : ℝ) ^ (⌈s.re / 2⌉₊ : ℕ) :=
    (mul_le_of_le_one_left hΓnn hπ1).trans (W1DensityNevanlinna.Gamma_le_ceil_pow (by linarith))
  have hY : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re)
      ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ) := dirichlet_sum_le (by linarith)
  gcongr

/-- **Off-strip (left) `Γ`-growth bound, `Re s ≤ −3`.** FE transport of `norm_xiNum_le_offstrip` to the
reflected point `1 − s` (which has `Re (1−s) = 1 − Re s ≥ 4`), via `xiNumerator_one_sub`. Together with
`norm_xiNum_le_offstrip` (right) and `CompletedZetaStripBound.norm_xiNum₀_le_on_strip` (strip interior,
e.g. on `[−3, 4]`), the three regions cover all of `ℂ` for the disk order bound. -/
theorem norm_xiNum_le_offstrip_left {s : ℂ} (hs : s.re ≤ -3) :
    ‖s * (s - 1) * completedRiemannZeta s‖
      ≤ ‖1 - s‖ * ‖(1 - s) - 1‖ *
        (((⌈(1 - s).re / 2⌉₊ : ℝ) ^ (⌈(1 - s).re / 2⌉₊ : ℕ)) *
          (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ))) := by
  rw [← W1DensityNevanlinna.xiNumerator_one_sub]
  exact norm_xiNum_le_offstrip (by rw [Complex.sub_re, Complex.one_re]; linarith)

/-- **Strip-interior region in the meromorphic (`Λ`) representation.** Via the bridge
`xiNum_completedRiemannZeta_eq`, the strip-interior bound (proved for `Λ₀`) is transported to
`s(s−1)·completedRiemannZeta` (with the harmless `+1`), so all three disk regions now bound the SAME
expression `s(s−1)·completedRiemannZeta s`. Requires `s ≠ 0, 1` (avoided on circles `|z|=r`, `r ≠ ½`). -/
theorem norm_xiNum_le_on_strip (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ 0 → s ≠ 1 →
      ‖s * (s - 1) * completedRiemannZeta s‖ ≤ C * (‖s‖ + 1) ^ 2 + 1 := by
  obtain ⟨C, hC0, hC⟩ := CompletedZetaStripBound.norm_xiNum₀_le_on_strip a b
  refine ⟨C, hC0, fun s ha hb hs0 hs1 => ?_⟩
  rw [CompletedZetaStripBound.xiNum_completedRiemannZeta_eq s hs0 hs1]
  calc ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
      ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖s * (s - 1) * completedRiemannZeta₀ s‖ + 1 := by rw [norm_one]
    _ ≤ C * (‖s‖ + 1) ^ 2 + 1 := by gcongr; exact hC s ha hb

/-- **Unified pointwise order bound for the entire ξ-numerator.** For all `s ≠ 0, 1`,
`‖s(s−1)·completedRiemannZeta s‖ ≤ C·(‖s‖+2)^(⌈‖s‖⌉₊+4)`. This is the order-1 growth bound (degree
linear in `‖s‖`, so `log‖xiNum‖ = O(‖s‖ log‖s‖)`), assembled from the three regional bounds by a
case-split on `Re s ∈ (−∞,−3] ∪ [−3,4] ∪ [4,∞)`. It is the keystone for the disk order bound
`M_Ξ(r) ≤ exp(C r log r)`: on a circle `|z|=r`, `‖s‖ = ‖½+iz‖ ≤ r + 1` and `Real.log_pow` turns the
bound into `log M_Ξ(r) ≤ (⌈r+1⌉+4)·log(r+3) + log C = O(r log r)`. RH-agnostic. -/
theorem norm_xiNum_order_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ‖s * (s - 1) * completedRiemannZeta s‖ ≤ C * (‖s‖ + 2) ^ (⌈‖s‖⌉₊ + 4) := by
  obtain ⟨Cstrip, hCs0, hCstrip⟩ := norm_xiNum_le_on_strip (-3) 4
  set Z₂ : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ) with hZdef
  have hZ0 : 0 ≤ Z₂ := tsum_nonneg (fun n => by positivity)
  set K : ℝ := max Cstrip Z₂ + 1 with hKdef
  have hK1 : 1 ≤ K := by
    have : 0 ≤ max Cstrip Z₂ := le_trans hCs0 (le_max_left _ _); rw [hKdef]; linarith
  have hZK : Z₂ ≤ K := by have := le_max_right Cstrip Z₂; rw [hKdef]; linarith
  have hCK1 : Cstrip ≤ K - 1 := by have := le_max_left Cstrip Z₂; rw [hKdef]; linarith
  refine ⟨K, hK1, fun s hs0 hs1 => ?_⟩
  set B : ℝ := ‖s‖ + 2 with hBdef
  have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  set M : ℕ := ⌈‖s‖⌉₊ with hMdef
  have hB1le : (1 : ℝ) ≤ B ^ (M + 4) := one_le_pow₀ hB1
  have hre : s.re ≤ ‖s‖ := (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
  have habs : -‖s‖ ≤ s.re := (abs_le.mp (Complex.abs_re_le_norm s)).1
  have hs_le : ‖s‖ ≤ B := by rw [hBdef]; linarith
  have hs1_le : ‖s - 1‖ ≤ B := by
    have := norm_sub_le s 1; rw [norm_one] at this; rw [hBdef]; linarith
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ ‖s‖ → ((⌈x⌉₊ : ℝ)) ^ (⌈x⌉₊) ≤ B ^ M := by
    intro x hx0 hxs
    have hbase : ((⌈x⌉₊ : ℝ)) ≤ B := by
      have h := Nat.ceil_lt_add_one hx0; rw [hBdef]; linarith
    have hexp : ⌈x⌉₊ ≤ M := Nat.ceil_le_ceil hxs
    calc ((⌈x⌉₊ : ℝ)) ^ (⌈x⌉₊) ≤ B ^ (⌈x⌉₊) := pow_le_pow_left₀ (by positivity) hbase _
      _ ≤ B ^ M := pow_le_pow_right₀ hB1 hexp
  have combine : ∀ (P Q x : ℝ), P ≤ B → Q ≤ B → 0 ≤ P → 0 ≤ Q → 0 ≤ x → x ≤ ‖s‖ →
      P * Q * ((⌈x⌉₊ : ℝ) ^ (⌈x⌉₊) * Z₂) ≤ K * B ^ (M + 4) := by
    intro P Q x hP hQ hP0 hQ0 hx0 hxs
    have h1 : P * Q ≤ B * B := mul_le_mul hP hQ hQ0 hB0
    have h2 : (⌈x⌉₊ : ℝ) ^ (⌈x⌉₊) * Z₂ ≤ B ^ M * K :=
      mul_le_mul (key x hx0 hxs) hZK hZ0 (by positivity)
    have h3 : P * Q * ((⌈x⌉₊ : ℝ) ^ (⌈x⌉₊) * Z₂) ≤ (B * B) * (B ^ M * K) :=
      mul_le_mul h1 h2 (mul_nonneg (by positivity) hZ0) (by positivity)
    calc P * Q * ((⌈x⌉₊ : ℝ) ^ (⌈x⌉₊) * Z₂) ≤ (B * B) * (B ^ M * K) := h3
      _ = K * B ^ (M + 2) := by ring
      _ ≤ K * B ^ (M + 4) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by omega)) (by linarith)
  rcases le_total s.re 4 with hle4 | hge4
  · rcases le_total (-3 : ℝ) s.re with hge3 | hle3
    · have hb := hCstrip s hge3 hle4 hs0 hs1
      have hsq : (‖s‖ + 1) ^ 2 ≤ B ^ (M + 4) := by
        calc (‖s‖ + 1) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) (by rw [hBdef]; linarith) 2
          _ ≤ B ^ (M + 4) := pow_le_pow_right₀ hB1 (by omega)
      have hprod : Cstrip * (‖s‖ + 1) ^ 2 ≤ (K - 1) * B ^ (M + 4) :=
        mul_le_mul hCK1 hsq (by positivity) (by linarith)
      calc ‖s * (s - 1) * completedRiemannZeta s‖ ≤ Cstrip * (‖s‖ + 1) ^ 2 + 1 := hb
        _ ≤ (K - 1) * B ^ (M + 4) + 1 := by linarith
        _ ≤ (K - 1) * B ^ (M + 4) + B ^ (M + 4) := by linarith
        _ = K * B ^ (M + 4) := by ring
    · have hb := norm_xiNum_le_offstrip_left hle3
      have hs3 : (3 : ℝ) ≤ ‖s‖ :=
        le_trans (le_abs.mpr (Or.inr (by linarith))) (Complex.abs_re_le_norm s)
      have hP : ‖1 - s‖ ≤ B := (norm_sub_le 1 s).trans (by rw [norm_one, hBdef]; linarith)
      have hQ : ‖(1 - s) - 1‖ ≤ B := by
        rw [show (1 - s) - 1 = -s by ring, norm_neg]; exact hs_le
      have hx0 : (0 : ℝ) ≤ (1 - s).re / 2 := by rw [Complex.sub_re, Complex.one_re]; linarith
      have hxs : (1 - s).re / 2 ≤ ‖s‖ := by rw [Complex.sub_re, Complex.one_re]; linarith
      exact hb.trans (combine _ _ _ hP hQ (norm_nonneg _) (norm_nonneg _) hx0 hxs)
  · have hb := norm_xiNum_le_offstrip hge4
    have hx0 : (0 : ℝ) ≤ s.re / 2 := by linarith
    have hxs : s.re / 2 ≤ ‖s‖ := by linarith
    exact hb.trans (combine _ _ _ hs_le hs1_le (norm_nonneg _) (norm_nonneg _) hx0 hxs)

/-- **Logarithmic order bound.** Taking `log` of `norm_xiNum_order_bound`:
`log‖s(s−1)·completedRiemannZeta s‖ ≤ C + (⌈‖s‖⌉₊+4)·log(‖s‖+2)`, manifestly `O(‖s‖ log‖s‖)`. The zero
case (`‖xiNum‖=0`) is handled by `Real.log_zero = 0 ≤` (RHS nonneg as the bounding value is `≥ 1`). This is
the form consumed by Nevanlinna's `characteristic`/`logCounting` (`log⁺ M(r)`); on a circle `|z|=r` with
`s=½+iz` (`‖s‖ ≤ r + 1`) it yields `log M_Ξ(r) = O(r log r)`. RH-agnostic. -/
theorem log_norm_xiNum_le :
    ∃ C : ℝ, ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      Real.log ‖s * (s - 1) * completedRiemannZeta s‖
        ≤ C + ((⌈‖s‖⌉₊ : ℝ) + 4) * Real.log (‖s‖ + 2) := by
  obtain ⟨C, hC1, hbound⟩ := norm_xiNum_order_bound
  refine ⟨Real.log C, fun s hs0 hs1 => ?_⟩
  have hb := hbound s hs0 hs1
  have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hP1 : (1 : ℝ) ≤ (‖s‖ + 2) ^ (⌈‖s‖⌉₊ + 4) := one_le_pow₀ (by linarith)
  have hY1 : (1 : ℝ) ≤ C * (‖s‖ + 2) ^ (⌈‖s‖⌉₊ + 4) := by nlinarith [hC1, hP1]
  have hlogY : Real.log (C * (‖s‖ + 2) ^ (⌈‖s‖⌉₊ + 4))
      = Real.log C + ((⌈‖s‖⌉₊ : ℝ) + 4) * Real.log (‖s‖ + 2) := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
  rcases eq_or_lt_of_le (norm_nonneg (s * (s - 1) * completedRiemannZeta s)) with h0 | hpos
  · rw [← h0, Real.log_zero, ← hlogY]; exact Real.log_nonneg hY1
  · exact (Real.log_le_log hpos hb).trans_eq hlogY

end XiOrderBound
