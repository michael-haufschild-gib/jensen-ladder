import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Derivative plus basepoint convergence

This module records a small analytic reconstruction lemma for complex-valued
functions on the whole complex plane.  Local uniform convergence of derivatives,
together with convergence at one basepoint, implies local uniform convergence of
the original functions.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

open Filter
open scoped Topology Filter

namespace JensenLadder
namespace DerivativeBasepointConvergence

variable {ι : Type*} {l : Filter ι}

/--
If complex functions are eventually differentiable on `ℂ`, their derivatives
converge locally uniformly to `deriv g`, and their values at a fixed basepoint
`w₀` converge to `g w₀`, then the functions themselves converge locally
uniformly to `g`.

The proof is the mean-value estimate on a closed ball containing the basepoint
and a small neighborhood of the point under consideration.
-/
theorem tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ_basepoint
    [NeBot l]
    (F : ι → ℂ → ℂ) (g : ℂ → ℂ) (w₀ : ℂ)
    (hF : ∀ᶠ n in l, Differentiable ℂ (F n))
    (hg : Differentiable ℂ g)
    (hderiv : TendstoLocallyUniformlyOn (fun n z => deriv (F n) z) (deriv g) l Set.univ)
    (hbase : Tendsto (fun n => F n w₀) l (𝓝 (g w₀))) :
    TendstoLocallyUniformlyOn F g l Set.univ := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  let R : ℝ := ‖x - w₀‖ + 2
  have hRpos : 0 < R := by
    unfold R
    positivity
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  let C : ℝ := ε / (2 * (R + 1))
  have hCpos : 0 < C := by
    unfold C
    positivity
  let t : Set ℂ := Metric.ball x 1
  have ht : t ∈ 𝓝[Set.univ] x := by
    simpa [t, nhdsWithin_univ] using Metric.ball_mem_nhds x zero_lt_one
  refine ⟨t, ht, ?_⟩
  have hK : IsCompact (Metric.closedBall w₀ R) := isCompact_closedBall w₀ R
  have hderiv_ball : TendstoUniformlyOn (fun n z => deriv (F n) z) (deriv g) l
      (Metric.closedBall w₀ R) := by
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hderiv
      (Metric.closedBall w₀ R) (Set.subset_univ _) hK
  have hderiv_ev : ∀ᶠ n in l, ∀ z ∈ Metric.closedBall w₀ R,
      dist (deriv g z) (deriv (F n) z) < C := by
    exact (Metric.tendstoUniformlyOn_iff.mp hderiv_ball C hCpos)
  have hbase_ev : ∀ᶠ n in l, dist (g w₀) (F n w₀) < ε / 2 := by
    exact (Metric.tendsto_nhds.mp hbase (ε / 2) (half_pos hε)).mono fun _ hn => by
      rwa [dist_comm]
  filter_upwards [hF, hderiv_ev, hbase_ev] with n hFn hdn hbase_n y hy
  have hyx : dist y x < 1 := by
    simpa [t] using hy
  have hy_norm_lt : ‖y - w₀‖ < R := by
    unfold R
    calc
      ‖y - w₀‖ = dist y w₀ := by simp [dist_eq_norm]
      _ ≤ dist y x + dist x w₀ := dist_triangle y x w₀
      _ < 1 + ‖x - w₀‖ := by
        have hxw : dist x w₀ = ‖x - w₀‖ := by simp [dist_eq_norm]
        nlinarith [hyx]
      _ < ‖x - w₀‖ + 2 := by nlinarith
  have hyK : y ∈ Metric.closedBall w₀ R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt hy_norm_lt
  have hbaseK : w₀ ∈ Metric.closedBall w₀ R := by
    simp [Metric.mem_closedBall, hRnonneg]
  have hdiff_at : ∀ z ∈ Metric.closedBall w₀ R,
      DifferentiableAt ℂ (fun w => F n w - g w) z := by
    intro z _
    exact (hFn z).sub (hg z)
  have hbound : ∀ z ∈ Metric.closedBall w₀ R,
      ‖deriv (fun w => F n w - g w) z‖ ≤ C := by
    intro z hz
    have hder : HasDerivAt (fun w => F n w - g w)
        (deriv (F n) z - deriv g z) z :=
      (hFn z).hasDerivAt.sub (hg z).hasDerivAt
    rw [hder.deriv]
    have hd := hdn z hz
    rw [dist_eq_norm] at hd
    simpa [norm_sub_rev] using (le_of_lt hd)
  have hmvt : ‖(F n y - g y) - (F n w₀ - g w₀)‖ ≤ C * ‖y - w₀‖ := by
    exact (convex_closedBall w₀ R).norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℂ) hdiff_at hbound hbaseK hyK
  have hy_norm_le : ‖y - w₀‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hyK
  have hCmul : C * ‖y - w₀‖ ≤ ε / 2 := by
    have hCnonneg : 0 ≤ C := le_of_lt hCpos
    have hmul_le : C * ‖y - w₀‖ ≤ C * R :=
      mul_le_mul_of_nonneg_left hy_norm_le hCnonneg
    have hCR : C * R ≤ ε / 2 := by
      unfold C
      have hdenpos : 0 < 2 * (R + 1) := by positivity
      have hRle : R ≤ R + 1 := by linarith
      have hfrac : R / (R + 1) ≤ 1 := by
        have hRp1 : 0 < R + 1 := by positivity
        rw [div_le_one hRp1]
        exact hRle
      have heq : ε / (2 * (R + 1)) * R = (ε / 2) * (R / (R + 1)) := by
        field_simp [ne_of_gt hdenpos, ne_of_gt (show (0 : ℝ) < R + 1 by positivity)]
      rw [heq]
      exact mul_le_of_le_one_right (le_of_lt (half_pos hε)) hfrac
    exact hmul_le.trans hCR
  have htri : ‖F n y - g y‖ ≤
      ‖(F n y - g y) - (F n w₀ - g w₀)‖ + ‖F n w₀ - g w₀‖ := by
    calc
      ‖F n y - g y‖ =
          ‖((F n y - g y) - (F n w₀ - g w₀)) + (F n w₀ - g w₀)‖ := by
            ring_nf
      _ ≤ ‖(F n y - g y) - (F n w₀ - g w₀)‖ + ‖F n w₀ - g w₀‖ :=
          norm_add_le _ _
  have hmain_norm : ‖F n y - g y‖ < ε := by
    have hbase_norm : ‖F n w₀ - g w₀‖ < ε / 2 := by
      rw [dist_eq_norm] at hbase_n
      simpa [norm_sub_rev] using hbase_n
    linarith
  rw [dist_eq_norm]
  simpa [norm_sub_rev] using hmain_norm

/--
Special case of
`tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ_basepoint`
with basepoint `0`.
-/
theorem tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ
    [NeBot l]
    (F : ι → ℂ → ℂ) (g : ℂ → ℂ)
    (hF : ∀ᶠ n in l, Differentiable ℂ (F n))
    (hg : Differentiable ℂ g)
    (hderiv : TendstoLocallyUniformlyOn (fun n z => deriv (F n) z) (deriv g) l Set.univ)
    (h0 : Tendsto (fun n => F n 0) l (𝓝 (g 0))) :
    TendstoLocallyUniformlyOn F g l Set.univ :=
  tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ_basepoint
    F g 0 hF hg hderiv h0

end DerivativeBasepointConvergence
end JensenLadder
