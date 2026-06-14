import JensenLadder.IntegrandHolomorphy

/-!
# Corridor geometry: SD-C2 ball predicates from clean inequalities

This file discharges the SD-C2 corridor hypotheses of the integrand-holomorphy
theorem (`JensenLadder.IntegrandHolomorphy`) for a concrete ball `ball ctr rad`,
reducing them to two real inequalities on the (certified) saddle-disk data:

```text
rad < ctr.re            -- ball in the right half-plane ⊆ slit plane
|ctr.im| + rad < π/4    -- ball inside the w-corridor Re(e^{2u}) > 0
```

From these, `integrand_differentiableOn_of_geom` produces holomorphy of the SD
integrand `exp(2k log u)·Φ(u)` on the ball. This removes hole-set (a)'s
corridor part: `hslit`, `hX`, `hcorr` are now derived; only the two numeric
inequalities on `(ctr, rad)` remain (provable by `norm_num` once concrete).

The corridor lower bound is the explicit constant
`c0 = exp(2(ctr.re − rad))·cos(2(|ctr.im| + rad)) > 0`.

## Honest scope

This formalizes the corridor/holomorphy geometry. The remaining hole-set (a)
items are the SD-C1/C2 *contour-piece* data (the four C¹ paths, their images in
the ball, loop closure) and the numeric connector/floor constants (hole-set (b)).
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

open Complex Metric

namespace JensenLadder
namespace CorridorGeometry

variable {ctr : ℂ} {rad : ℝ}

theorem re_lb_of_mem_ball {u : ℂ} (hu : u ∈ ball ctr rad) : ctr.re - rad < u.re := by
  have h := Metric.mem_ball.mp hu
  rw [Complex.dist_eq] at h
  have h2 : |(u - ctr).re| ≤ ‖u - ctr‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h2
  have h3 : |u.re - ctr.re| < rad := lt_of_le_of_lt h2 h
  rw [abs_lt] at h3; linarith [h3.1]

theorem re_le_of_mem_ball {u : ℂ} (hu : u ∈ ball ctr rad) : u.re ≤ ctr.re + rad := by
  have h := Metric.mem_ball.mp hu
  rw [Complex.dist_eq] at h
  have h2 : |(u - ctr).re| ≤ ‖u - ctr‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h2
  have h3 : |u.re - ctr.re| < rad := lt_of_le_of_lt h2 h
  rw [abs_lt] at h3; linarith [h3.2]

theorem im_abs_lt_of_mem_ball {u : ℂ} (hu : u ∈ ball ctr rad) : |u.im| < |ctr.im| + rad := by
  have h := Metric.mem_ball.mp hu
  rw [Complex.dist_eq] at h
  have h2 : |(u - ctr).im| ≤ ‖u - ctr‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h2
  have h3 : |u.im - ctr.im| < rad := lt_of_le_of_lt h2 h
  have h4 : |u.im| - |ctr.im| ≤ |u.im - ctr.im| := abs_sub_abs_le_abs_sub _ _
  linarith

/-- The ball sits in the slit plane when `rad < ctr.re`. -/
theorem ball_subset_slitPlane (hre : rad < ctr.re) :
    ∀ u ∈ ball ctr rad, u ∈ slitPlane := fun u hu =>
  Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [re_lb_of_mem_ball hu]))

theorem cos_corner_pos (hrad : 0 < rad) (him : |ctr.im| + rad < Real.pi / 4) :
    0 < Real.cos (2 * (|ctr.im| + rad)) := by
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨?_, by linarith⟩
  have := Real.pi_pos; have := abs_nonneg ctr.im; linarith

/-- The w-corridor lower bound `Re(e^{2u}) ≥ c0` on the ball, with
`c0 = exp(2(ctr.re − rad))·cos(2(|ctr.im| + rad))`. -/
theorem corridor_lower_of_mem_ball (hrad : 0 < rad) (him : |ctr.im| + rad < Real.pi / 4)
    {u : ℂ} (hu : u ∈ ball ctr rad) :
    Real.exp (2 * (ctr.re - rad)) * Real.cos (2 * (|ctr.im| + rad))
      ≤ (Complex.exp (2 * u)).re := by
  have e1 : (2 * u).re = 2 * u.re := by simp [Complex.mul_re]
  have e2 : (2 * u).im = 2 * u.im := by simp [Complex.mul_im]
  rw [Complex.exp_re, e1, e2]
  have hpipos := Real.pi_pos
  have hexp_le : Real.exp (2 * (ctr.re - rad)) ≤ Real.exp (2 * u.re) :=
    Real.exp_le_exp.mpr (by linarith [re_lb_of_mem_ball hu])
  have huim : |2 * u.im| ≤ 2 * (|ctr.im| + rad) := by
    rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have := im_abs_lt_of_mem_ball hu; linarith
  have hcos_le : Real.cos (2 * (|ctr.im| + rad)) ≤ Real.cos (2 * u.im) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |2 * u.im|)
      (y := 2 * (|ctr.im| + rad)) (abs_nonneg _) (by linarith) huim
    rwa [Real.cos_abs] at h
  exact mul_le_mul hexp_le hcos_le (cos_corner_pos hrad him).le (Real.exp_pos _).le

/-- **Holomorphy of the SD integrand from clean ball geometry (SD-C2 discharged).**
If `0 < rad`, `rad < ctr.re`, and `|ctr.im| + rad < π/4`, then the SD integrand
`exp(2k log u)·Φ(u)` is holomorphic on `ball ctr rad`. -/
theorem integrand_differentiableOn_of_geom (k : ℂ) (hrad : 0 < rad)
    (hre : rad < ctr.re) (him : |ctr.im| + rad < Real.pi / 4) :
    DifferentiableOn ℂ (IntegrandHolomorphy.integrand k) (ball ctr rad) :=
  IntegrandHolomorphy.integrand_differentiableOn k
    (mul_pos (Real.exp_pos _) (cos_corner_pos hrad him))
    (ball_subset_slitPlane hre)
    (fun _ hu => re_le_of_mem_ball hu)
    (fun _ hu => corridor_lower_of_mem_ball hrad him hu)

end CorridorGeometry
end JensenLadder
