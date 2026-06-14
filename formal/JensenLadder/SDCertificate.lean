import JensenLadder.CorridorGeometry
import JensenLadder.AffineContour

/-!
# SD-C end-to-end capstone (affine straight-segment contour)

This file assembles the formal SD-C development into a single theorem for the
actual affine SD contour: the positive real ray, the straight saddle segment
`u* + t·e`, and the two straight connectors. It composes

* `CorridorGeometry.integrand_differentiableOn_of_geom` (SD-C0 holomorphy from
  the corridor inequalities),
* `AffineContour.affine_hasDerivAt` / `affine_mem_ball` /
  `affine_integrand_intervalIntegrable` (SD-C1/C2 contour-piece predicates), and
* `ContourLegality.connector_relative_error_of_holomorphic` (SD-C3 connector
  bound → SD-C4 nonvanishing + relative error),

into `sdc_relative_error_affine`: the true (real-ray) moment integral is nonzero
and a controlled unit-disk perturbation of the saddle-segment certificate.

## The exact remaining hypotheses (the honest hole set)

After this assembly the ONLY ungrounded inputs are numerical facts about the
specific contour, each interval-certified outside Lean:

* **corridor** `0<rad`, `rad<ctr.re`, `|ctr.im|+rad<π/4` — the ball sits in the
  slit plane and the w-corridor (saddle-disk geometry);
* **endpoint memberships** — each affine piece's two endpoints lie in the ball;
* **loop closure** `e0a..e1b` — the four pieces chain into a closed loop;
* **connector sup bounds** `C0,C1` and **margin** `τ0<μ` with `μ ≤ ‖∫_seg‖` —
  interval-certified (mpmath.iv; `fable_sdc_margin_iv_v1`, all rows ≤1e-12).

Notably the saddle-method conditions `G_u(u*)=0`, `|G_uu|≥γ2`, `Φ(u*)≠0` are NOT
hypotheses here: the contour-homotopy legality is proved for ANY C¹ contour with
a primitive on the ball, so the saddle structure enters only through the
(numerical) connector sup bounds, not as separate Lean obligations.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

open Complex Metric

namespace JensenLadder
namespace SDCertificate

/-- **SD-C end-to-end certificate (affine contour).**
For the SD integrand `f = exp(2k log u)·Φ`, the real-ray moment integral is a
controlled unit-disk perturbation of the saddle-segment certificate and is
nonzero — derived from the corridor geometry, the affine contour-piece data, the
loop closure, the connector sup bounds, and the certified margin. -/
theorem sdc_relative_error_affine
    (k : ℂ) {ctr : ℂ} {rad : ℝ}
    {ar vr : ℂ} {tr0 tr1 : ℝ}
    {sa sv : ℂ} {ss0 ss1 : ℝ}
    {b0 w0 : ℂ} {p0 q0 : ℝ}
    {b1 w1 : ℂ} {p1 q1 : ℝ}
    {C0 C1 mu : ℝ}
    (hrad : 0 < rad) (hre : rad < ctr.re) (him : |ctr.im| + rad < Real.pi / 4)
    (hr0 : ar + tr0 • vr ∈ ball ctr rad) (hr1 : ar + tr1 • vr ∈ ball ctr rad)
    (hs0 : sa + ss0 • sv ∈ ball ctr rad) (hs1 : sa + ss1 • sv ∈ ball ctr rad)
    (h00 : b0 + p0 • w0 ∈ ball ctr rad) (h0q : b0 + q0 • w0 ∈ ball ctr rad)
    (h10 : b1 + p1 • w1 ∈ ball ctr rad) (h1q : b1 + q1 • w1 ∈ ball ctr rad)
    (e0a : b0 + p0 • w0 = ar + tr1 • vr) (e0b : b0 + q0 • w0 = sa + ss1 • sv)
    (e1a : b1 + p1 • w1 = sa + ss0 • sv) (e1b : b1 + q1 • w1 = ar + tr0 • vr)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0,
        ‖IntegrandHolomorphy.integrand k (b0 + t • w0) * w0‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1,
        ‖IntegrandHolomorphy.integrand k (b1 + t • w1) * w1‖ ≤ C1)
    (hmu : mu ≤ ‖∫ t in ss0..ss1, IntegrandHolomorphy.integrand k (sa + t • sv) * sv‖)
    (htau : C0 * |q0 - p0| + C1 * |q1 - p1| < mu) :
    ∃ eps : ℂ,
      (∫ t in tr0..tr1, IntegrandHolomorphy.integrand k (ar + t • vr) * vr)
          = (∫ t in ss0..ss1, IntegrandHolomorphy.integrand k (sa + t • sv) * sv) * (1 + eps)
      ∧ ‖eps‖ ≤ (C0 * |q0 - p0| + C1 * |q1 - p1|) / mu
      ∧ ‖eps‖ < 1
      ∧ (∫ t in tr0..tr1, IntegrandHolomorphy.integrand k (ar + t • vr) * vr) ≠ 0 := by
  have hf := CorridorGeometry.integrand_differentiableOn_of_geom k hrad hre him
  have hcont := hf.continuousOn
  exact ContourLegality.connector_relative_error_of_holomorphic hf
    (fun t _ => AffineContour.affine_hasDerivAt ar vr t)
    (fun t _ => AffineContour.affine_hasDerivAt sa sv t)
    (fun t _ => AffineContour.affine_hasDerivAt b0 w0 t)
    (fun t _ => AffineContour.affine_hasDerivAt b1 w1 t)
    (AffineContour.affine_mem_ball hr0 hr1) (AffineContour.affine_mem_ball hs0 hs1)
    (AffineContour.affine_mem_ball h00 h0q) (AffineContour.affine_mem_ball h10 h1q)
    (AffineContour.affine_integrand_intervalIntegrable hcont
      (AffineContour.affine_mem_ball hr0 hr1))
    (AffineContour.affine_integrand_intervalIntegrable hcont
      (AffineContour.affine_mem_ball hs0 hs1))
    (AffineContour.affine_integrand_intervalIntegrable hcont
      (AffineContour.affine_mem_ball h00 h0q))
    (AffineContour.affine_integrand_intervalIntegrable hcont
      (AffineContour.affine_mem_ball h10 h1q))
    e0a e0b e1a e1b hb0 hb1 hmu htau

end SDCertificate
end JensenLadder
