import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# W1-density: Nevanlinna order-theory bricks toward `Σ_ρ 1/(¼+γ²) < ∞`

First bricks of the W1-density formalization roadmap
(`docs/rh/w1_density_formalization_roadmap_20260614.md`), whose goal is to discharge the standing
absolute-summability hypothesis `Summable (1/|u_ρ|)` of `JensenLadder.CarrierCanonicalProduct` for the
actual nontrivial zeros of ζ — making the whole carrier backbone *unconditional*.

This file builds on mathlib's Nevanlinna value-distribution theory
(`Mathlib/Analysis/Complex/ValueDistribution/`). RH-agnostic; does not prove RH; Theorem M does not prove
RH by itself.

## Roadmap status
- **Brick (FMT counting half), HERE:** `logCounting_le_characteristic` — `N(r,f) ≤ T(r,f)`.
- Remaining (research-scale, see roadmap): ξ growth bound `T(r,ξ)=O(r log r)` (Stirling + ζ strip growth);
  the convergence-exponent bridge `N(r)=O(r log r) ⟹ Σ 1/|zₙ|² < ∞`; discharge into `CarrierCanonicalProduct`.
-/

open ValueDistribution

namespace W1DensityNevanlinna

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a : WithTop E}

/-- **First Main Theorem counting bound `N(r) ≤ T(r)`.** The Nevanlinna logarithmic counting function
`logCounting f a` (which counts, with multiplicity, how often `f` attains `a` in `|z|≤r`) is dominated by
the characteristic `characteristic f a = proximity f a + logCounting f a`, since the proximity function is
non-negative. This is the order-theory primitive that turns a growth bound on `T(r,f)` into a bound on the
number of `a`-points (with `a = 0`: the zeros) of `f`. -/
theorem logCounting_le_characteristic (r : ℝ) :
    logCounting f a r ≤ characteristic f a r := by
  simp only [characteristic, Pi.add_apply]
  exact le_add_of_nonneg_left (proximity_nonneg r)

/-- **Convergence-exponent / summability brick (brick 4 core).** If the moduli grow at least like
`(n+1)^θ` with `θ > 1/2`, then `Σ_n 1/(g n)² < ∞`. A counting bound `N(R) = O(R log R)` supplies such a
`θ` (in fact any `θ < 1`), so this is the order-theory step that converts the zero-counting bound into the
genus-0 absolute summability `Σ_ρ 1/(¼+γ²) < ∞`. General real analysis (comparison with the `p`-series);
reusable. -/
theorem summable_inv_sq_of_rpow_le (g : ℕ → ℝ) {c θ : ℝ} (hc : 0 < c) (hθ : 1 / 2 < θ)
    (hg : ∀ n : ℕ, c * ((n : ℝ) + 1) ^ θ ≤ g n) : Summable (fun n => 1 / (g n) ^ 2) := by
  have hcpos : ∀ n : ℕ, 0 < c * ((n : ℝ) + 1) ^ θ := fun n => by positivity
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * θ)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (2 * θ)).mpr (by linarith)
    refine h.congr (fun n => ?_)
    rw [abs_of_nonneg (by positivity)]
  have hcomp : Summable (fun n : ℕ => 1 / c ^ 2 * (1 / ((n : ℝ) + 1) ^ (2 * θ))) := hbase.mul_left _
  refine hcomp.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have hb : c ^ 2 * ((n : ℝ) + 1) ^ (2 * θ) ≤ (g n) ^ 2 := by
    have h1 : (c * ((n : ℝ) + 1) ^ θ) ^ 2 ≤ (g n) ^ 2 := by gcongr; exact hg n
    have h2 : (c * ((n : ℝ) + 1) ^ θ) ^ 2 = c ^ 2 * ((n : ℝ) + 1) ^ (2 * θ) := by
      rw [mul_pow, ← Real.rpow_natCast (((n : ℝ) + 1) ^ θ) 2, ← Real.rpow_mul (by positivity)]
      norm_num [mul_comm]
    linarith [h2 ▸ h1]
  calc 1 / (g n) ^ 2 ≤ 1 / (c ^ 2 * ((n : ℝ) + 1) ^ (2 * θ)) :=
        one_div_le_one_div_of_le (by positivity) hb
    _ = 1 / c ^ 2 * (1 / ((n : ℝ) + 1) ^ (2 * θ)) := (one_div_mul_one_div _ _).symm

open MeasureTheory Set in
/-- **Γ-factor growth bound (brick 2 input).** `‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0`, directly from Euler's
integral representation `Γ(s)=∫₀^∞ e^{-t} t^{s-1} dt` and `|t^{s-1}| = t^{Re s - 1}`. This is the input
to the ξ growth/order bound (combined with the `ζ` Dirichlet bound on `Re>1` and Phragmén–Lindelöf):
the *crude* integral bound suffices for order `1`, so no sharp complex Stirling asymptotic is needed. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs]
  calc ‖Complex.GammaIntegral s‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (s - 1)‖ := by
        rw [Complex.GammaIntegral]; exact norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-- **ζ Dirichlet growth bound (brick 2 input, `Re>1` edge).** `‖ζ(s)‖ ≤ Σ_n 1/((n+1)^{Re s})` for
`Re s > 1`, from the Dirichlet series and the triangle inequality for `tsum`. The right-hand side is the
value of `ζ` at the real point `Re s`, so this is `‖ζ(σ+it)‖ ≤ ζ(σ)` — a bound constant in `Im s`, the
`Re>1` boundary input for the Phragmén–Lindelöf interpolation giving ξ's order. -/
theorem norm_riemannZeta_le_tsum {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := by
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ = 1 / ((n : ℝ) + 1) ^ s.re := by
    intro n
    rw [norm_div, norm_one]
    congr 1
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have hsumm : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖) := by
    simp_rw [hnorm]
    have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
    exact h.congr (fun n => by rw [abs_of_nonneg (by positivity)])
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc ‖∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hsumm
    _ = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := tsum_congr hnorm

/-- **Archimedean-factor growth bound (brick 2).** `‖Γℝ(s)‖ ≤ π^{-Re s/2}·Γ(Re s/2)` for `Re s > 0`,
where `Γℝ(s) = π^{-s/2}Γ(s/2)` is the archimedean Euler factor of the completed zeta. Combines the
Γ-factor bound `norm_Gamma_le_Gamma_re` with `‖π^{-s/2}‖ = π^{-Re s/2}`. The completed-zeta factor of the
ξ growth/order bound. -/
theorem norm_Gammaℝ_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]; congr 1; simp
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have h := norm_Gamma_le_Gamma_re (s := s / 2) (by rw [hre]; linarith)
    rwa [hre] at h
  rw [hπ]
  gcongr

/-- **Completed-zeta growth bound on `Re>1` (brick 2 assembly).** `‖Λ(s)‖ ≤ (π^{-σ/2}Γ(σ/2))·ζ(σ)` for
`Re s = σ > 1`, assembling the archimedean factor (`norm_Gammaℝ_le`) and the ζ-Dirichlet bound
(`norm_riemannZeta_le_tsum`) through `Λ(s) = Γℝ(s)·ζ(s)` (`riemannZeta_def_of_ne_zero`). This is the
`Re>1` edge bound on the completed ξ-numerator; the ξ order bound follows by multiplying the `½s(s−1)`
polynomial, FE-transporting to `Re<0`, and Phragmén–Lindelöf across the strip. -/
theorem norm_completedRiemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖completedRiemannZeta s‖
      ≤ (Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2)) * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
  have hΓℝ : Complex.Gammaℝ s ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [hn] at hs
    have hre : ((-(2 * (n : ℂ))).re) = -(2 * (n : ℝ)) := by simp
    rw [hre] at hs
    have : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
    linarith
  have hzeta := riemannZeta_def_of_ne_zero hs0
  rw [eq_div_iff hΓℝ] at hzeta
  rw [← hzeta, norm_mul, mul_comm]
  gcongr
  · exact norm_Gammaℝ_le (by linarith)
  · exact norm_riemannZeta_le_tsum hs

/-- **Entire ξ-numerator growth bound on `Re>1` (brick 2).** `s(s−1)·Λ(s)` is the entire Riemann ξ-numerator
(`= 2·ξ(s)`, the `½s(s−1)` poles-cancellation of `Λ`). On `Re s > 1` it is bounded by
`‖s‖·‖s−1‖·(π^{-σ/2}Γ(σ/2))·ζ(σ)`, extending the `Λ` bound by the polynomial factor. This is the `Re>1`
edge bound on the entire function whose zeros are the nontrivial zeros `ρ`; FE-transport to `Re<0`
(`completedRiemannZeta_one_sub`) + Phragmén–Lindelöf then give the order bound on circles. -/
theorem norm_xiNumerator_le {s : ℂ} (hs : 1 < s.re) :
    ‖s * (s - 1) * completedRiemannZeta s‖
      ≤ ‖s‖ * ‖s - 1‖ *
        ((Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2)) * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re)) := by
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_completedRiemannZeta_le hs

/-- **Order-1 Gamma growth bound (brick 2).** `Γ(x) ≤ ⌈x⌉^⌈x⌉` for `x ≥ 2`, from monotonicity of `Γ` on
`[2,∞)` (`Real.Gamma_strictMonoOn_Ici`), `Γ(n) = (n−1)!` (`Real.Gamma_nat_eq_factorial`), and
`n! ≤ nⁿ` (`Nat.factorial_le_pow`). Taking logs gives `log Γ(x) ≤ ⌈x⌉·log⌈x⌉ = O(x log x)` — the order-1
growth of the Γ-factor, the analytic input that turns the `Re>1` ξ-bound into `‖ξ‖ ≤ exp(C·R log R)`. -/
theorem Gamma_le_ceil_pow {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ ((⌈x⌉₊ : ℝ)) ^ (⌈x⌉₊ : ℕ) := by
  set m : ℕ := ⌈x⌉₊ with hm
  have hxm : x ≤ (m : ℝ) := Nat.le_ceil x
  have hm2 : 2 ≤ m := by have h : (2 : ℝ) ≤ (m : ℝ) := le_trans hx hxm; exact_mod_cast h
  have hmono : Real.Gamma x ≤ Real.Gamma (m : ℝ) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hx)
      (Set.mem_Ici.mpr (by exact_mod_cast hm2)) hxm
  have hfact : Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) := by
    have hcast : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
      have h1 : 1 ≤ m := by omega
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast, Real.Gamma_nat_eq_factorial]
  have hnat : Nat.factorial (m - 1) ≤ m ^ m :=
    calc Nat.factorial (m - 1) ≤ (m - 1) ^ (m - 1) := Nat.factorial_le_pow (m - 1)
      _ ≤ m ^ (m - 1) := Nat.pow_le_pow_left (Nat.sub_le m 1) (m - 1)
      _ ≤ m ^ m := Nat.pow_le_pow_right (by omega) (Nat.sub_le m 1)
  refine hmono.trans (hfact.le.trans ?_)
  calc (Nat.factorial (m - 1) : ℝ) ≤ ((m ^ m : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (m : ℝ) ^ (m : ℕ) := by push_cast; ring

/-- **Functional-equation symmetry of the entire ξ-numerator (brick 2).** `s(s−1)Λ(s)` is invariant under
`s ↦ 1−s`: `(1−s)((1−s)−1)Λ(1−s) = s(s−1)Λ(s)`, from `Λ(1−s)=Λ(s)` (`completedRiemannZeta_one_sub`) and
`(1−s)(−s) = s(s−1)`. This transports the `Re>1` edge bound to the `Re<0` edge. -/
theorem xiNumerator_one_sub (s : ℂ) :
    (1 - s) * ((1 - s) - 1) * completedRiemannZeta (1 - s)
      = s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannZeta_one_sub]; ring

/-- **Re<0 edge bound for the ξ-numerator (brick 2).** By FE-transport (`xiNumerator_one_sub`) of the
`Re>1` bound (`norm_xiNumerator_le`) to the reflected point `1−s` (which has `Re>1` when `Re s<0`). With the
`Re>1` edge (`norm_xiNumerator_le`), both edges of the critical strip are now bounded — the inputs for the
Phragmén–Lindelöf / three-lines interpolation giving the circle/order bound. -/
theorem norm_xiNumerator_le_of_re_lt {s : ℂ} (hs : s.re < 0) :
    ‖s * (s - 1) * completedRiemannZeta s‖
      ≤ ‖1 - s‖ * ‖(1 - s) - 1‖ *
        ((Real.pi ^ (-(1 - s).re / 2) * Real.Gamma ((1 - s).re / 2)) *
          (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 - s).re)) := by
  rw [← xiNumerator_one_sub]
  exact norm_xiNumerator_le (by rw [Complex.sub_re, Complex.one_re]; linarith)

end W1DensityNevanlinna
