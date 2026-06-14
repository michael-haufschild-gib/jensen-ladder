import JensenLadder.ContourLegality

/-!
# Affine contour pieces: discharging the SD-C1/C2 contour-piece predicates

The SD-C3 contour theorems (`JensenLadder.ContourLegality`) take, for each of the
four straight pieces (real ray, saddle segment `u* + t·e`, two connectors), the
hypotheses: `HasDerivAt γ (γ' t) t`, image-in-ball, and `IntervalIntegrable`.
For an **affine** path `γ(t) = a + t·v` these are all derivable:

* `affine_hasDerivAt` — the derivative is the constant `v` (so `γ' = fun _ => v`).
* `affine_mem_ball` — the image of `[t0,t1]` lies in any ball containing the two
  endpoints (convexity of the ball).
* `affine_integrand_intervalIntegrable` — the integrand `f(γ t)·v` is interval
  integrable when `f` is continuous on the ball and the path stays in the ball.

This removes the contour-piece part of hole-set (a) for the straight-segment SD
contour: the four `hγ*`/`him*`/integrability hypotheses reduce to the endpoint
memberships (which follow from the corridor geometry) plus continuity of the
integrand. What remains as hypotheses are the SD-C1 saddle data and the loop
closure equalities.

## Honest scope

These are unconditional lemmas about affine paths. Their use for the actual SD
contour still takes the saddle/cap geometry (the endpoints `a + tᵢ·v ∈ ball`) as
numerically-certified input. Theorem M is proven, but Theorem M does not prove RH
by itself.
-/

open Complex Metric

namespace JensenLadder
namespace AffineContour

/-- An affine path `t ↦ a + t • v` (real parameter, complex value) has constant
derivative `v`. -/
theorem affine_hasDerivAt (a v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add a

/-- A point of an affine segment lies in the segment between its endpoints. -/
theorem affine_mem_segment {a v : ℂ} {t0 t1 t : ℝ} (hle : t0 ≤ t1)
    (ht : t ∈ Set.Icc t0 t1) :
    a + t • v ∈ segment ℝ (a + t0 • v) (a + t1 • v) := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have : t = t0 := le_antisymm ht.2 ht.1
    subst this; exact left_mem_segment ℝ _ _
  · have hd : (0 : ℝ) < t1 - t0 := by linarith
    set s : ℝ := (t - t0) / (t1 - t0) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hd.le
    have hs1 : s ≤ 1 := by rw [hs, div_le_one hd]; linarith [ht.2]
    have hco : (1 - s) * t0 + s * t1 = t := by
      rw [hs]; field_simp; ring
    refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
    have hcomb : (1 - s) • (a + t0 • v) + s • (a + t1 • v)
        = a + ((1 - s) * t0 + s * t1) • v := by module
    rw [hcomb, hco]

/-- The image of `[t0,t1]` under an affine path lies in any ball containing the
two endpoints. -/
theorem affine_mem_ball {a v ctr : ℂ} {rad t0 t1 : ℝ}
    (h0 : a + t0 • v ∈ ball ctr rad) (h1 : a + t1 • v ∈ ball ctr rad) :
    ∀ t ∈ Set.uIcc t0 t1, a + t • v ∈ ball ctr rad := by
  intro t ht
  rcases le_total t0 t1 with hle | hle
  · rw [Set.uIcc_of_le hle] at ht
    exact (convex_ball ctr rad).segment_subset h0 h1 (affine_mem_segment hle ht)
  · rw [Set.uIcc_of_ge hle] at ht
    exact (convex_ball ctr rad).segment_subset h1 h0 (affine_mem_segment hle ht)

/-- The integrand `f(γ t)·v` of an affine path is interval integrable when `f` is
continuous on a ball containing the path image. -/
theorem affine_integrand_intervalIntegrable {f : ℂ → ℂ} {a v ctr : ℂ} {rad t0 t1 : ℝ}
    (hf : ContinuousOn f (ball ctr rad))
    (hmem : ∀ t ∈ Set.uIcc t0 t1, a + t • v ∈ ball ctr rad) :
    IntervalIntegrable (fun t => f (a + t • v) * v) MeasureTheory.volume t0 t1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul _ continuousOn_const
  apply hf.comp _ hmem
  exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn

end AffineContour
end JensenLadder
