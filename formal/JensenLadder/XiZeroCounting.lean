import JensenLadder.HurwitzRealRootedLimit
import JensenLadder.XiOrderBound

/-!
# Zero counting for the carrier `Ξ = xiEntire` via Jensen's inequality (W1-density, brick 3)

Toward `∑_ρ 1/(¼+γ²) < ∞` (the carrier `CarrierCanonicalProduct` summability hypothesis). The plan,
using mathlib's `AnalyticOnNhd.sum_divisor_le` (Jensen counting inequality):

* `xiEntire` is entire (`xiEntire_differentiable`) with zeros = the ordinates `z_ρ = -i(ρ-½)`.
* **center**: `xiEntire (-3I/2) = completedRiemannZeta 2 ≠ 0` (`Re = 2 > 1`), a concrete nonvanishing
  point for the Jensen ball center (`ξ(½) ≠ 0` is unavailable in mathlib, so we center off the line).
* **growth**: `‖xiEntire z‖ ≤ ½·C·(‖½+iz‖+2)^(⌈‖½+iz‖⌉₊+4)` (`norm_xiEntire_le`), from the unified order
  bound `XiOrderBound.norm_xiNum_order_bound` and the pole-cancellation `xi_pole_cancel`.

These feed `AnalyticOnNhd.sum_divisor_le` (with `R = 2r`) to give `n(r) = O(r log r)`, then a
convergence-exponent argument over the divisor gives `∑_ρ 1/|z_ρ|² < ∞ ⟹ ∑_ρ 1/(¼+γ²) < ∞`.
**RH-agnostic; Theorem M does not prove RH by itself.**
-/

open Complex JensenLadder.HurwitzBridge Metric

namespace XiZeroCounting

/-- `xiEntire` at `z = -3I/2` (i.e. `s = ½ + iz = 2`) equals the completed zeta at `2`. -/
theorem xiEntire_neg_three_halves_I :
    xiEntire (-(3 / 2) * I) = completedRiemannZeta 2 := by
  unfold xiEntire
  have hs : (1 / 2 + I * (-(3 / 2) * I) : ℂ) = 2 := by
    rw [show I * (-(3 / 2) * I) = -(3 / 2) * (I * I) by ring, Complex.I_mul_I]; ring
  rw [hs, ← xi_pole_cancel 2 (by norm_num) (by norm_num)]; ring

/-- **Concrete nonvanishing center for the Jensen ball.** `xiEntire (-3I/2) = completedRiemannZeta 2 ≠ 0`
since `riemannZeta 2 ≠ 0` (`Re 2 = 2 > 1`) and `completedRiemannZeta 2 = riemannZeta 2 · Gammaℝ 2`. -/
theorem xiEntire_neg_three_halves_I_ne_zero : xiEntire (-(3 / 2) * I) ≠ 0 := by
  rw [xiEntire_neg_three_halves_I]
  intro h
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact hz (by rw [riemannZeta_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), h, zero_div])

/-- **Pointwise order bound for `xiEntire`.** `‖xiEntire z‖ ≤ ½·C·(‖½+iz‖+2)^(⌈‖½+iz‖⌉₊+4)` away from
the (removable) points `½+iz ∈ {0,1}` (`z = ±i/2`). The order-1 growth of the carrier `Ξ`, inherited
from `XiOrderBound.norm_xiNum_order_bound` via the pole-cancellation identity. -/
theorem norm_xiEntire_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ,
    (1 / 2 + I * z) ≠ 0 → (1 / 2 + I * z) ≠ 1 →
    ‖xiEntire z‖ ≤ (1 / 2) * (C * (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)) := by
  obtain ⟨C, hC1, hb⟩ := XiOrderBound.norm_xiNum_order_bound
  refine ⟨C, hC1, fun z hz0 hz1 => ?_⟩
  have hpc : xiEntire z
      = (1 / 2) * ((1 / 2 + I * z) * ((1 / 2 + I * z) - 1) * completedRiemannZeta (1 / 2 + I * z)) := by
    unfold xiEntire; rw [xi_pole_cancel _ hz0 hz1]
  rw [hpc, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have := hb (1 / 2 + I * z) hz0 hz1
  gcongr

/-- **Uniform sphere bound for `xiEntire`.** For `R > ½` (so `½+iz ≠ 0,1` on the sphere),
`‖xiEntire z‖ ≤ ½·C·(R+5/2)^(⌈R+1/2⌉₊+4)` for all `z` with `‖z‖ = R`. This is the single value `M(R)`
required by `AnalyticOnNhd.sum_divisor_le`: from the pointwise bound `norm_xiEntire_le` plus
`‖½+iz‖ ≤ R+½` and monotonicity of `(t+2)^(⌈t⌉₊+4)` in `t`. -/
theorem norm_xiEntire_le_sphere : ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℝ, 1 / 2 < R → ∀ z : ℂ, ‖z‖ = R →
    ‖xiEntire z‖ ≤ (1 / 2) * (C * (R + 5 / 2) ^ (⌈R + 1 / 2⌉₊ + 4)) := by
  obtain ⟨C, hC1, hb⟩ := norm_xiEntire_le
  refine ⟨C, hC1, fun R hR z hz => ?_⟩
  have hIz : ‖I * z‖ = R := by rw [norm_mul, norm_I, one_mul, hz]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hlow : R - 1 / 2 ≤ ‖1 / 2 + I * z‖ := by
    have h := norm_sub_le (1 / 2 + I * z) (1 / 2 : ℂ)
    rw [show (1 / 2 + I * z) - 1 / 2 = I * z by ring, hIz, hhalf] at h
    linarith
  have hz0 : (1 / 2 + I * z) ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz1 : (1 / 2 + I * z) ≠ 1 := by
    intro h
    have hval : ‖I * z‖ = 1 / 2 := by
      rw [show I * z = (1 / 2 + I * z) - 1 / 2 by ring, h]; norm_num
    rw [hIz] at hval; linarith
  have ht : ‖1 / 2 + I * z‖ ≤ R + 1 / 2 := by
    calc ‖1 / 2 + I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖I * z‖ := norm_add_le _ _
      _ = R + 1 / 2 := by rw [hIz, hhalf]; ring
  refine (hb z hz0 hz1).trans ?_
  have hpow : (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)
      ≤ (R + 5 / 2) ^ (⌈R + 1 / 2⌉₊ + 4) := by
    calc (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)
        ≤ (R + 5 / 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (R + 5 / 2) ^ (⌈R + 1 / 2⌉₊ + 4) :=
          pow_le_pow_right₀ (by linarith) (by have := Nat.ceil_le_ceil ht; omega)
  have hmul : C * (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)
      ≤ C * (R + 5 / 2) ^ (⌈R + 1 / 2⌉₊ + 4) := mul_le_mul_of_nonneg_left hpow (by linarith)
  linarith

/-- **All-`z` ball/order bound for `xiEntire`** (no exclusion). `‖xiEntire z‖ ≤ ½·C·(‖z‖+5/2)^(⌈‖z‖+1/2⌉₊+4)`
for every `z`, including the two removable points `½+iz ∈ {0,1}` (`z = ±i/2`), where `xiEntire = 1/2` and
the bound holds since its RHS is `≥ ½`. This is the reusable order bound `‖Ξ(z)‖ ≤ g(‖z‖)` with `g`
monotone; on any sphere `sphere c R` it gives `‖Ξ(z)‖ ≤ g(‖c‖+R)`, the uniform `M` for
`AnalyticOnNhd.sum_divisor_le` at center `c = -3I/2` (where `Ξ ≠ 0`). -/
theorem norm_xiEntire_le_ball : ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ,
    ‖xiEntire z‖ ≤ (1 / 2) * (C * (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4)) := by
  obtain ⟨C, hC1, hb⟩ := norm_xiEntire_le
  refine ⟨C, hC1, fun z => ?_⟩
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hP1 : (1 : ℝ) ≤ (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4) := one_le_pow₀ (by linarith)
  have hmono : (1 / 2) * (C * (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4))
      ≤ (1 / 2) * (C * (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4)) := by
    have ht : ‖1 / 2 + I * z‖ ≤ ‖z‖ + 1 / 2 := by
      calc ‖1 / 2 + I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖I * z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 / 2 := by rw [norm_mul, norm_I, one_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; ring
    have hpow : (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)
        ≤ (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4) := by
      calc (‖1 / 2 + I * z‖ + 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4)
          ≤ (‖z‖ + 5 / 2) ^ (⌈‖1 / 2 + I * z‖⌉₊ + 4) := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4) :=
            pow_le_pow_right₀ (by linarith) (by have := Nat.ceil_le_ceil ht; omega)
    have := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ C)
    linarith
  by_cases h0 : (1 / 2 + I * z) = 0
  · have hval : xiEntire z = 1 / 2 := by unfold xiEntire; rw [h0]; ring
    rw [hval, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; nlinarith [hC1, hP1]
  · by_cases h1 : (1 / 2 + I * z) = 1
    · have hval : xiEntire z = 1 / 2 := by unfold xiEntire; rw [h1]; ring
      rw [hval, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; nlinarith [hC1, hP1]
    · exact (hb z h0 h1).trans hmono

/-- **Monotone uniform order bound.** `‖z‖ ≤ ρ ⟹ ‖xiEntire z‖ ≤ ½·C·(ρ+5/2)^(⌈ρ+1/2⌉₊+4)`. The
ball bound `norm_xiEntire_le_ball` made monotone in the radius `ρ`, the form needed for a uniform
bound on a sphere of given radius. -/
theorem xiEntire_le_of_norm_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ (ρ : ℝ) (z : ℂ), ‖z‖ ≤ ρ →
    ‖xiEntire z‖ ≤ (1 / 2) * (C * (ρ + 5 / 2) ^ (⌈ρ + 1 / 2⌉₊ + 4)) := by
  obtain ⟨C, hC1, hb⟩ := norm_xiEntire_le_ball
  refine ⟨C, hC1, fun ρ z hz => ?_⟩
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  refine (hb z).trans ?_
  have hpow : (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4) ≤ (ρ + 5 / 2) ^ (⌈ρ + 1 / 2⌉₊ + 4) := by
    calc (‖z‖ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4)
        ≤ (ρ + 5 / 2) ^ (⌈‖z‖ + 1 / 2⌉₊ + 4) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (ρ + 5 / 2) ^ (⌈ρ + 1 / 2⌉₊ + 4) :=
          pow_le_pow_right₀ (by linarith)
            (by have := Nat.ceil_le_ceil (show ‖z‖ + 1 / 2 ≤ ρ + 1 / 2 by linarith); omega)
  have := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ C)
  linarith

/-- **Jensen zero-counting bound for the carrier `Ξ = xiEntire`.** For every `r > 0`, the number of
zeros of `xiEntire` in `closedBall (-3I/2) r` (counted with multiplicity, `∑ᶠ` of the divisor) is
`≤ log(M(r)/‖completedRiemannZeta 2‖)/log 2`, where `M(r) = ½·C·(2r+4)^(⌈2r+2⌉₊+4)`. Since
`log M(r) = O(r log r)`, this is the counting bound `n(r) = O(r log r)`. Proved by
`AnalyticOnNhd.sum_divisor_le` (Jensen) with center `-3I/2` (`Ξ ≠ 0` there), radius `r`, outer radius
`R = 2r` (so `log(R/r) = log 2`), and the uniform sphere bound `M(r)` from `xiEntire_le_of_norm_le`.
This is the W1-density counting input; a convergence-exponent argument over the divisor then gives
`∑_ρ 1/(¼+γ²) < ∞`. RH-agnostic; Theorem M does not prove RH by itself. -/
theorem xiEntire_divisor_count_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r →
    ((∑ᶠ u, (MeromorphicOn.divisor xiEntire (closedBall (-(3 / 2) * I) |r|)) u : ℤ) : ℝ)
      ≤ Real.log ((1 / 2) * (C * (2 * r + 4) ^ (⌈2 * r + 2⌉₊ + 4)) / ‖completedRiemannZeta 2‖)
          / Real.log 2 := by
  obtain ⟨C, hC1, hub⟩ := xiEntire_le_of_norm_le
  refine ⟨C, hC1, fun r hr => ?_⟩
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  set M : ℝ := (1 / 2) * (C * (2 * r + 4) ^ (⌈2 * r + 2⌉₊ + 4)) with hMdef
  have hcnorm : ‖(-(3 / 2) * I : ℂ)‖ = 3 / 2 := by
    rw [norm_mul, norm_neg, norm_I, mul_one, Complex.norm_div]; norm_num
  have fbound : ∀ z ∈ sphere (-(3 / 2) * I) |2 * r|, ‖xiEntire z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq, abs_of_pos hr2] at hz
    have hzc : ‖z‖ ≤ 2 * r + 3 / 2 := by
      have ht : ‖z‖ ≤ ‖z - (-(3 / 2) * I)‖ + ‖(-(3 / 2) * I : ℂ)‖ := by
        have := norm_add_le (z - (-(3 / 2) * I)) (-(3 / 2) * I); simpa using this
      rw [hcnorm] at ht; rw [hz] at ht; linarith
    have hbd := hub (2 * r + 3 / 2) z hzc
    rw [hMdef]
    have he1 : (2 * r + 3 / 2) + 5 / 2 = 2 * r + 4 := by ring
    have he2 : (2 * r + 3 / 2) + 1 / 2 = 2 * r + 2 := by ring
    rw [he1, he2] at hbd; exact hbd
  have hMpos : (4 : ℝ) ≤ (2 * r + 4) ^ (⌈2 * r + 2⌉₊ + 4) := by
    have hself : (2 * r + 4) ≤ (2 * r + 4) ^ (⌈2 * r + 2⌉₊ + 4) := le_self_pow₀ (by linarith) (by omega)
    linarith
  have hM1 : 1 ≤ M := by rw [hMdef]; nlinarith [hC1, hMpos]
  have happ := AnalyticOnNhd.sum_divisor_le (c := -(3 / 2) * I) (r := r) (R := 2 * r) (M := M)
    (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos hr2]; linarith)
    hM1
    (fun x _ => xiEntire_differentiable.analyticAt x)
    xiEntire_neg_three_halves_I_ne_zero
    fbound
  rw [xiEntire_neg_three_halves_I] at happ
  rw [show 2 * r / r = 2 by field_simp] at happ
  exact happ

/-- **Reduction `|u_ρ| ≥ γ²`.** For any `ρ`, `‖ρ(1−ρ)‖ ≥ (Im ρ)²` (since `‖ρ‖ ≥ |Im ρ|` and
`‖1−ρ‖ ≥ |Im(1−ρ)| = |Im ρ|`). With `u_ρ = ρ(1−ρ)`, this reduces the carrier's summability
`Σ 1/|u_ρ|` to the simpler ordinate sum `Σ 1/γ²`. -/
theorem norm_rho_mul_one_sub_ge_im_sq (ρ : ℂ) : (ρ.im) ^ 2 ≤ ‖ρ * (1 - ρ)‖ := by
  rw [norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖1 - ρ‖ := by
    have := Complex.abs_im_le_norm (1 - ρ)
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this; exact this
  calc (ρ.im) ^ 2 = |ρ.im| * |ρ.im| := by rw [← sq_abs, sq]
    _ ≤ ‖ρ‖ * ‖1 - ρ‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- **Carrier summability reduction.** If the ordinate sum `Σ_i 1/(Im ρ_i)²` converges and every
`Im ρ_i ≠ 0`, then the carrier inverse-eigenvalue sum `Σ_i 1/‖ρ_i(1−ρ_i)‖ = Σ_i 1/|u_{ρ_i}|`
converges — discharging the `CarrierCanonicalProduct` summability hypothesis from `Σ 1/γ² < ∞`. -/
theorem summable_inv_norm_u_of_summable_inv_im_sq {ι : Type*} (ρ : ι → ℂ)
    (hγ : Summable (fun i => 1 / (ρ i).im ^ 2)) (hne : ∀ i, (ρ i).im ≠ 0) :
    Summable (fun i => 1 / ‖ρ i * (1 - ρ i)‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hγ
  have him : (0 : ℝ) < (ρ i).im ^ 2 := by have := hne i; positivity
  exact one_div_le_one_div_of_le him (norm_rho_mul_one_sub_ge_im_sq (ρ i))

end XiZeroCounting
