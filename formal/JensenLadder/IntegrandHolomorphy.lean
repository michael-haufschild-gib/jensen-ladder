import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import JensenLadder.ContourLegality

/-!
# SD-C0 holomorphy of the steepest-descent integrand

This file discharges the holomorphy hypothesis `hf` of the SD-C3 contour theorems
(`JensenLadder.ContourLegality`) for the *concrete* steepest-descent integrand

```text
f(u) = exp(2 k log u) · Φ(u),   Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6π n² e^{5u/2}) e^{−π n² e^{2u}}
```

(the completed-ξ theta kernel; the `n = 0` term vanishes, so the sum is taken over `ℕ`).

## Route

* `exp(2 k log u)` is holomorphic on any ball inside the slit plane (`Re u > 0`
  suffices), via `Complex.differentiableAt_log` + `exp`.
* `Φ` is holomorphic on a *w-corridor ball* — one on which `Re u ≤ X` and
  `0 < c0 ≤ Re(e^{2u})` — by the Weierstrass M-test
  (`Complex.differentiableOn_tsum_of_summable_norm`): each term is entire, and on
  the corridor `‖phiTerm n u‖ ≤ uBound X c0 n` with `∑ uBound` summable (the
  Gaussian `e^{−π c0 n²}` dominates the polynomial prefactor — the theta-corridor
  bound of `docs/rh/sd_contour_legality_certificate.md`).
* The product is holomorphic, giving `integrand_differentiableOn`.

`sdc3_connector_bound_concrete` then feeds this into
`ContourLegality.connector_bound_of_holomorphic`, so the SD-C3 connector bound
for the concrete integrand no longer assumes holomorphy: it is derived from the
corridor geometry (`hslit`, `hX`, `hcorr`) plus the SD-C1/C2 contour data.

## Honest scope

The corridor facts `hslit : ball ⊆ slitPlane`, `hX`, `hcorr` (and the contour
geometry of SD-C1/C2) enter as hypotheses — they are the numerically-certified
SD geometry. What is now *formal* (previously assumed) is the analytic SD-C0
statement that the integrand is holomorphic on that geometry. Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

open Complex Metric

namespace JensenLadder
namespace IntegrandHolomorphy

noncomputable section

/-- One term of the completed-ξ theta kernel:
`(4π²n⁴ e^{9u/2} − 6π n² e^{5u/2})·exp(−π n² e^{2u})`. -/
def phiTerm (n : ℕ) (u : ℂ) : ℂ :=
  ((((4 * Real.pi ^ 2 * (n : ℝ) ^ 4 : ℝ)) : ℂ) * Complex.exp (((9 / 2 : ℝ) : ℂ) * u)
      - (((6 * Real.pi * (n : ℝ) ^ 2 : ℝ)) : ℂ) * Complex.exp (((5 / 2 : ℝ) : ℂ) * u))
    * Complex.exp (-((((Real.pi * (n : ℝ) ^ 2 : ℝ)) : ℂ) * Complex.exp (2 * u)))

/-- The completed-ξ theta kernel as a series (the `n = 0` term vanishes). -/
def Phi (u : ℂ) : ℂ := ∑' n : ℕ, phiTerm n u

/-- Sup bound on `‖phiTerm n‖` over a corridor ball with `Re u ≤ X`,
`c0 ≤ Re(e^{2u})`. -/
def uBound (X c0 : ℝ) (n : ℕ) : ℝ :=
  (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * X / 2)
      + 6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * X / 2))
    * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * c0))

theorem differentiable_phiTerm (n : ℕ) : Differentiable ℂ (phiTerm n) := by
  unfold phiTerm
  fun_prop

/-- `∑ n^k e^{−c n²}` is summable for `c > 0` (dominate by a geometric series via
`n² ≥ n`). -/
theorem summable_pow_mul_exp_neg_sq (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(c * (n : ℝ) ^ 2))) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have hle : Real.exp (-(c * (n : ℝ) ^ 2)) ≤ Real.exp (-c) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (n : ℕ) ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
      exact_mod_cast this
    nlinarith [hc.le]
  calc (n : ℝ) ^ k * Real.exp (-(c * (n : ℝ) ^ 2))
      ≤ (n : ℝ) ^ k * Real.exp (-c) ^ n :=
        mul_le_mul_of_nonneg_left hle (by positivity)

theorem summable_uBound (X c0 : ℝ) (hc0 : 0 < c0) : Summable (uBound X c0) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < Real.pi * c0 := by positivity
  have h4 : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-(Real.pi * c0 * (n : ℝ) ^ 2))) :=
    summable_pow_mul_exp_neg_sq 4 hc
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-(Real.pi * c0 * (n : ℝ) ^ 2))) :=
    summable_pow_mul_exp_neg_sq 2 hc
  have hsum := (h4.mul_left (4 * Real.pi ^ 2 * Real.exp (9 * X / 2))).add
    (h2.mul_left (6 * Real.pi * Real.exp (5 * X / 2)))
  refine hsum.congr (fun n => ?_)
  simp only [uBound]
  rw [show -(Real.pi * (n : ℝ) ^ 2 * c0) = -(Real.pi * c0 * (n : ℝ) ^ 2) by ring]
  ring

theorem phiTerm_norm_le (n : ℕ) {X c0 : ℝ} {u : ℂ}
    (hX : u.re ≤ X) (hc0 : c0 ≤ (Complex.exp (2 * u)).re) :
    ‖phiTerm n u‖ ≤ uBound X c0 n := by
  have hpi := Real.pi_pos
  rw [phiTerm, uBound, norm_mul]
  apply mul_le_mul
  · refine (norm_sub_le _ _).trans ?_
    gcongr
    · calc ‖(((4 * Real.pi ^ 2 * (n : ℝ) ^ 4 : ℝ)) : ℂ) * Complex.exp (((9 / 2 : ℝ) : ℂ) * u)‖
          = (4 * Real.pi ^ 2 * (n : ℝ) ^ 4) * Real.exp ((9 / 2 : ℝ) * u.re) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              Complex.norm_exp, Complex.re_ofReal_mul]
        _ ≤ (4 * Real.pi ^ 2 * (n : ℝ) ^ 4) * Real.exp (9 * X / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (by linarith)
    · calc ‖(((6 * Real.pi * (n : ℝ) ^ 2 : ℝ)) : ℂ) * Complex.exp (((5 / 2 : ℝ) : ℂ) * u)‖
          = (6 * Real.pi * (n : ℝ) ^ 2) * Real.exp ((5 / 2 : ℝ) * u.re) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              Complex.norm_exp, Complex.re_ofReal_mul]
        _ ≤ (6 * Real.pi * (n : ℝ) ^ 2) * Real.exp (5 * X / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (by linarith)
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [Complex.neg_re, Complex.re_ofReal_mul]
    have : Real.pi * (n : ℝ) ^ 2 * c0 ≤ Real.pi * (n : ℝ) ^ 2 * (Complex.exp (2 * u)).re :=
      mul_le_mul_of_nonneg_left hc0 (by positivity)
    linarith
  · exact norm_nonneg _
  · positivity

/-- **Φ is holomorphic on a w-corridor ball** (Weierstrass M-test). -/
theorem phi_differentiableOn {ctr : ℂ} {rad X c0 : ℝ} (hc0 : 0 < c0)
    (hX : ∀ u ∈ ball ctr rad, u.re ≤ X)
    (hcorr : ∀ u ∈ ball ctr rad, c0 ≤ (Complex.exp (2 * u)).re) :
    DifferentiableOn ℂ Phi (ball ctr rad) :=
  Complex.differentiableOn_tsum_of_summable_norm (summable_uBound X c0 hc0)
    (fun n => (differentiable_phiTerm n).differentiableOn) isOpen_ball
    (fun n w hw => phiTerm_norm_le n (hX w hw) (hcorr w hw))

/-- The SD-C steepest-descent integrand `exp(2 k log u)·Φ(u)`. -/
def integrand (k : ℂ) (u : ℂ) : ℂ := Complex.exp (2 * k * Complex.log u) * Phi u

/-- **SD-C0 holomorphy of the concrete SD integrand — discharges `hf`.**
On a ball inside the slit plane (`Re u > 0` suffices) carrying the corridor
bounds `Re u ≤ X` and `0 < c0 ≤ Re(e^{2u})`, the integrand `exp(2 k log u)·Φ(u)`
is holomorphic. -/
theorem integrand_differentiableOn (k : ℂ) {ctr : ℂ} {rad X c0 : ℝ} (hc0 : 0 < c0)
    (hslit : ∀ u ∈ ball ctr rad, u ∈ slitPlane)
    (hX : ∀ u ∈ ball ctr rad, u.re ≤ X)
    (hcorr : ∀ u ∈ ball ctr rad, c0 ≤ (Complex.exp (2 * u)).re) :
    DifferentiableOn ℂ (integrand k) (ball ctr rad) := by
  have hexp : DifferentiableOn ℂ (fun u => Complex.exp (2 * k * Complex.log u)) (ball ctr rad) := by
    intro u hu
    have hlog : DifferentiableAt ℂ Complex.log u := Complex.differentiableAt_log (hslit u hu)
    exact (((differentiableAt_const (2 * k)).mul hlog).cexp).differentiableWithinAt
  exact hexp.mul (phi_differentiableOn hc0 hX hcorr)

/-- **SD-C3 connector bound for the concrete integrand, holomorphy discharged.**
Specializes `ContourLegality.connector_bound_of_holomorphic` to `f = integrand k`,
with the holomorphy hypothesis supplied by `integrand_differentiableOn`. The
remaining hypotheses are the SD-C1/C2 contour geometry. -/
theorem sdc3_connector_bound_concrete (k : ℂ) {ctr : ℂ} {rad X c0 : ℝ}
    {γr γr' : ℝ → ℂ} {ar br : ℝ}
    {γs γs' : ℝ → ℂ} {cs ds : ℝ}
    {γ0 γ0' : ℝ → ℂ} {p0 q0 : ℝ}
    {γ1 γ1' : ℝ → ℂ} {p1 q1 : ℝ}
    {C0 C1 : ℝ}
    (hc0 : 0 < c0)
    (hslit : ∀ u ∈ ball ctr rad, u ∈ slitPlane)
    (hXc : ∀ u ∈ ball ctr rad, u.re ≤ X)
    (hcorr : ∀ u ∈ ball ctr rad, c0 ≤ (Complex.exp (2 * u)).re)
    (hγr : ∀ t ∈ Set.uIcc ar br, HasDerivAt γr (γr' t) t)
    (hγs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt γs (γs' t) t)
    (hγ0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt γ0 (γ0' t) t)
    (hγ1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt γ1 (γ1' t) t)
    (himr : ∀ t ∈ Set.uIcc ar br, γr t ∈ ball ctr rad)
    (hims : ∀ t ∈ Set.uIcc cs ds, γs t ∈ ball ctr rad)
    (him0 : ∀ t ∈ Set.uIcc p0 q0, γ0 t ∈ ball ctr rad)
    (him1 : ∀ t ∈ Set.uIcc p1 q1, γ1 t ∈ ball ctr rad)
    (hir : IntervalIntegrable (fun t => integrand k (γr t) * γr' t) MeasureTheory.volume ar br)
    (his : IntervalIntegrable (fun t => integrand k (γs t) * γs' t) MeasureTheory.volume cs ds)
    (hi0 : IntervalIntegrable (fun t => integrand k (γ0 t) * γ0' t) MeasureTheory.volume p0 q0)
    (hi1 : IntervalIntegrable (fun t => integrand k (γ1 t) * γ1' t) MeasureTheory.volume p1 q1)
    (e0a : γ0 p0 = γr br) (e0b : γ0 q0 = γs ds)
    (e1a : γ1 p1 = γs cs) (e1b : γ1 q1 = γr ar)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0, ‖integrand k (γ0 t) * γ0' t‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1, ‖integrand k (γ1 t) * γ1' t‖ ≤ C1) :
    ‖(∫ t in ar..br, integrand k (γr t) * γr' t)
        - (∫ t in cs..ds, integrand k (γs t) * γs' t)‖
      ≤ C0 * |q0 - p0| + C1 * |q1 - p1| :=
  ContourLegality.connector_bound_of_holomorphic
    (integrand_differentiableOn k hc0 hslit hXc hcorr)
    hγr hγs hγ0 hγ1 himr hims him0 him1 hir his hi0 hi1 e0a e0b e1a e1b hb0 hb1

end

end IntegrandHolomorphy
end JensenLadder
