import Mathlib.Analysis.Complex.HasPrimitives
import JensenLadder.LogTransfer

/-!
# SD-C3 contour deformation legality and connector/tail bound

This file formalizes the deterministic analytic core of the SD-C3 obligation in
the steepest-descent moment certificate (`docs/rh/sd_contour_legality_certificate.md`):
the *contour-homotopy legality* step plus the *connector/tail bound*.

The moment used by the E1K cumulants is

```text
M(k) = 2 ∫_{Γ_real} exp(G(u,k)) du
```

but the numerical evaluator `M_sd` integrates over a finite saddle *segment*
`Γ_seg`.  SD-C3 must certify that replacing `Γ_real` by `Γ_seg` is legal and
that the omitted connector pieces are small:

```text
| ∫_{Γ_real} - ∫_{Γ_seg} | ≤ τ0.
```

## Route

The integrand `f(u) = exp(2 k log u) Φ(u)` is holomorphic on the SD-C0 domain
`Ω` (which is `0 ∉ Ω`, single-valued `log`, convergent `Φ`).  On a **disk**
`Ω = ball ctr rad` Morera's theorem (mathlib `DifferentiableOn.isExactOn_ball`)
supplies a global primitive `g`.  Then the contour integral of `f` over any C¹
path `γ` collapses by the fundamental theorem of calculus to `g(γ b) - g(γ a)`
(`integral_eq_sub`).  Path-independence (`path_integral_eq_of_eq_endpoints`) and
the closed-loop telescoping that powers the connector bound
(`connector_bound`, `connector_bound_of_holomorphic`) are then pure algebra.

## What is proved vs. assumed

* **Proved (from holomorphy on a disk):** the deformation is legal — the
  real-ray integral and the saddle-segment integral differ by exactly the two
  connector integrals, which are bounded by `length × sup`.
* **Proved (consumer chain):** feeding that bound into the SD-C4 core
  (`JensenLadder.LogTransfer.exists_relative_error`) certifies the true moment
  is nonzero and a controlled unit-disk perturbation of the certificate
  (`connector_relative_error`, `connector_relative_error_of_holomorphic`).
* **Assumed (separate SD-C obligations):** that the specific SD integrand is
  `DifferentiableOn ℂ f (ball ctr rad)` with the contour pieces inside the ball
  (the SD-C0/SD-C2 geometry, numerically certified), and that the connector
  constants and the certificate floor `μ` satisfy `τ0 < μ` (the interval
  obligation).  These enter as hypotheses, exactly as `tau`/`mu` enter SD-C4.
-/

open Complex Metric
open scoped Interval
open MeasureTheory intervalIntegral

namespace JensenLadder
namespace ContourLegality

/-- **Contour fundamental theorem of calculus.**
If `g` is a primitive of `f` along the C¹ path `γ` on `[a,b]` — that is
`HasDerivAt γ (γ' t) t` and `HasDerivAt g (f (γ t)) (γ t)` for `t ∈ [a,b]` — then
the contour integral `∫ f(γ) γ'` equals `g (γ b) - g (γ a)`. -/
theorem integral_eq_sub
    {g f : ℂ → ℂ} {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hg : ∀ t ∈ Set.uIcc a b, HasDerivAt g (f (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => f (γ t) * γ' t) volume a b) :
    (∫ t in a..b, f (γ t) * γ' t) = g (γ b) - g (γ a) := by
  have hcomp : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => g (γ t)) (f (γ t) * γ' t) t := by
    intro t ht
    have h := (hg t ht).scomp t (hγ t ht)
    have he : γ' t • f (γ t) = f (γ t) * γ' t := by rw [smul_eq_mul, mul_comm]
    rw [he] at h
    simpa [Function.comp] using h
  simpa using integral_eq_sub_of_hasDerivAt hcomp hint

/-- **Path independence = contour-homotopy legality (primitive form).**
Two C¹ paths sharing a primitive `g` of `f` and the same endpoints have equal
contour integrals.  This is the legality statement: the integral does not depend
on the chosen contour, only on its endpoints. -/
theorem path_integral_eq_of_eq_endpoints
    {g f : ℂ → ℂ}
    {γ₁ γ₁' : ℝ → ℂ} {a₁ b₁ : ℝ}
    {γ₂ γ₂' : ℝ → ℂ} {a₂ b₂ : ℝ}
    (hγ₁ : ∀ t ∈ Set.uIcc a₁ b₁, HasDerivAt γ₁ (γ₁' t) t)
    (hγ₂ : ∀ t ∈ Set.uIcc a₂ b₂, HasDerivAt γ₂ (γ₂' t) t)
    (hg₁ : ∀ t ∈ Set.uIcc a₁ b₁, HasDerivAt g (f (γ₁ t)) (γ₁ t))
    (hg₂ : ∀ t ∈ Set.uIcc a₂ b₂, HasDerivAt g (f (γ₂ t)) (γ₂ t))
    (hi₁ : IntervalIntegrable (fun t => f (γ₁ t) * γ₁' t) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun t => f (γ₂ t) * γ₂' t) volume a₂ b₂)
    (hstart : γ₁ a₁ = γ₂ a₂) (hend : γ₁ b₁ = γ₂ b₂) :
    (∫ t in a₁..b₁, f (γ₁ t) * γ₁' t) = (∫ t in a₂..b₂, f (γ₂ t) * γ₂' t) := by
  rw [integral_eq_sub hγ₁ hg₁ hi₁, integral_eq_sub hγ₂ hg₂ hi₂, hstart, hend]

/-- **SD-C3 connector decomposition + bound (primitive form).**
Given a common primitive `g` of `f` along all four pieces of the deformation loop
— the real ray `r`, the saddle segment `s`, and the two connectors `0`, `1` that
close the loop (`γ0 : Γ_real-end → Γ_seg-end`, `γ1 : Γ_seg-start → Γ_real-start`)
— the difference of the real-ray and saddle-segment integrals telescopes to minus
the sum of the connector integrals, hence is bounded by the connector lengths
times their sup norms. -/
theorem connector_bound
    {g f : ℂ → ℂ}
    {γr γr' : ℝ → ℂ} {ar br : ℝ}
    {γs γs' : ℝ → ℂ} {cs ds : ℝ}
    {γ0 γ0' : ℝ → ℂ} {p0 q0 : ℝ}
    {γ1 γ1' : ℝ → ℂ} {p1 q1 : ℝ}
    {C0 C1 : ℝ}
    (hγr : ∀ t ∈ Set.uIcc ar br, HasDerivAt γr (γr' t) t)
    (hγs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt γs (γs' t) t)
    (hγ0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt γ0 (γ0' t) t)
    (hγ1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt γ1 (γ1' t) t)
    (hgr : ∀ t ∈ Set.uIcc ar br, HasDerivAt g (f (γr t)) (γr t))
    (hgs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt g (f (γs t)) (γs t))
    (hg0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt g (f (γ0 t)) (γ0 t))
    (hg1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt g (f (γ1 t)) (γ1 t))
    (hir : IntervalIntegrable (fun t => f (γr t) * γr' t) volume ar br)
    (his : IntervalIntegrable (fun t => f (γs t) * γs' t) volume cs ds)
    (hi0 : IntervalIntegrable (fun t => f (γ0 t) * γ0' t) volume p0 q0)
    (hi1 : IntervalIntegrable (fun t => f (γ1 t) * γ1' t) volume p1 q1)
    (e0a : γ0 p0 = γr br) (e0b : γ0 q0 = γs ds)
    (e1a : γ1 p1 = γs cs) (e1b : γ1 q1 = γr ar)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0, ‖f (γ0 t) * γ0' t‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1, ‖f (γ1 t) * γ1' t‖ ≤ C1) :
    ‖(∫ t in ar..br, f (γr t) * γr' t) - (∫ t in cs..ds, f (γs t) * γs' t)‖
      ≤ C0 * |q0 - p0| + C1 * |q1 - p1| := by
  have Ir := integral_eq_sub hγr hgr hir
  have Is := integral_eq_sub hγs hgs his
  have I0 := integral_eq_sub hγ0 hg0 hi0
  have I1 := integral_eq_sub hγ1 hg1 hi1
  have key : (∫ t in ar..br, f (γr t) * γr' t) - (∫ t in cs..ds, f (γs t) * γs' t)
      = -((∫ t in p0..q0, f (γ0 t) * γ0' t) + (∫ t in p1..q1, f (γ1 t) * γ1' t)) := by
    rw [Ir, Is, I0, I1, e0a, e0b, e1a, e1b]; ring
  rw [key, norm_neg]
  have n0 : ‖∫ t in p0..q0, f (γ0 t) * γ0' t‖ ≤ C0 * |q0 - p0| :=
    norm_integral_le_of_norm_le_const hb0
  have n1 : ‖∫ t in p1..q1, f (γ1 t) * γ1' t‖ ≤ C1 * |q1 - p1| :=
    norm_integral_le_of_norm_le_const hb1
  exact (norm_add_le _ _).trans (add_le_add n0 n1)

/-- **SD-C3 connector bound from holomorphy on a disk (headline).**
If `f` is holomorphic on a disk `ball ctr rad` and the four contour pieces of the
deformation loop lie in that disk, then the real-ray vs. saddle-segment moment
difference is bounded by the connector lengths times their sup norms.  The
primitive is produced from holomorphy by Morera's theorem
(`DifferentiableOn.isExactOn_ball`); no primitive is assumed. -/
theorem connector_bound_of_holomorphic
    {f : ℂ → ℂ} {ctr : ℂ} {rad : ℝ}
    {γr γr' : ℝ → ℂ} {ar br : ℝ}
    {γs γs' : ℝ → ℂ} {cs ds : ℝ}
    {γ0 γ0' : ℝ → ℂ} {p0 q0 : ℝ}
    {γ1 γ1' : ℝ → ℂ} {p1 q1 : ℝ}
    {C0 C1 : ℝ}
    (hf : DifferentiableOn ℂ f (ball ctr rad))
    (hγr : ∀ t ∈ Set.uIcc ar br, HasDerivAt γr (γr' t) t)
    (hγs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt γs (γs' t) t)
    (hγ0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt γ0 (γ0' t) t)
    (hγ1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt γ1 (γ1' t) t)
    (himr : ∀ t ∈ Set.uIcc ar br, γr t ∈ ball ctr rad)
    (hims : ∀ t ∈ Set.uIcc cs ds, γs t ∈ ball ctr rad)
    (him0 : ∀ t ∈ Set.uIcc p0 q0, γ0 t ∈ ball ctr rad)
    (him1 : ∀ t ∈ Set.uIcc p1 q1, γ1 t ∈ ball ctr rad)
    (hir : IntervalIntegrable (fun t => f (γr t) * γr' t) volume ar br)
    (his : IntervalIntegrable (fun t => f (γs t) * γs' t) volume cs ds)
    (hi0 : IntervalIntegrable (fun t => f (γ0 t) * γ0' t) volume p0 q0)
    (hi1 : IntervalIntegrable (fun t => f (γ1 t) * γ1' t) volume p1 q1)
    (e0a : γ0 p0 = γr br) (e0b : γ0 q0 = γs ds)
    (e1a : γ1 p1 = γs cs) (e1b : γ1 q1 = γr ar)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0, ‖f (γ0 t) * γ0' t‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1, ‖f (γ1 t) * γ1' t‖ ≤ C1) :
    ‖(∫ t in ar..br, f (γr t) * γr' t) - (∫ t in cs..ds, f (γs t) * γs' t)‖
      ≤ C0 * |q0 - p0| + C1 * |q1 - p1| := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  exact connector_bound hγr hγs hγ0 hγ1
    (fun t ht => hg _ (himr t ht)) (fun t ht => hg _ (hims t ht))
    (fun t ht => hg _ (him0 t ht)) (fun t ht => hg _ (him1 t ht))
    hir his hi0 hi1 e0a e0b e1a e1b hb0 hb1

/-- **SD-C3 → SD-C4 pipeline (primitive form).**
Combine the connector bound with the SD-C4 log-transfer core: if additionally the
certificate value `∫_seg` has norm `≥ μ` and `τ0 = C0·|·| + C1·|·| < μ`, then the
true moment integral is a controlled unit-disk perturbation of the certificate
and is nonzero. -/
theorem connector_relative_error
    {g f : ℂ → ℂ}
    {γr γr' : ℝ → ℂ} {ar br : ℝ}
    {γs γs' : ℝ → ℂ} {cs ds : ℝ}
    {γ0 γ0' : ℝ → ℂ} {p0 q0 : ℝ}
    {γ1 γ1' : ℝ → ℂ} {p1 q1 : ℝ}
    {C0 C1 mu : ℝ}
    (hγr : ∀ t ∈ Set.uIcc ar br, HasDerivAt γr (γr' t) t)
    (hγs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt γs (γs' t) t)
    (hγ0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt γ0 (γ0' t) t)
    (hγ1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt γ1 (γ1' t) t)
    (hgr : ∀ t ∈ Set.uIcc ar br, HasDerivAt g (f (γr t)) (γr t))
    (hgs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt g (f (γs t)) (γs t))
    (hg0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt g (f (γ0 t)) (γ0 t))
    (hg1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt g (f (γ1 t)) (γ1 t))
    (hir : IntervalIntegrable (fun t => f (γr t) * γr' t) volume ar br)
    (his : IntervalIntegrable (fun t => f (γs t) * γs' t) volume cs ds)
    (hi0 : IntervalIntegrable (fun t => f (γ0 t) * γ0' t) volume p0 q0)
    (hi1 : IntervalIntegrable (fun t => f (γ1 t) * γ1' t) volume p1 q1)
    (e0a : γ0 p0 = γr br) (e0b : γ0 q0 = γs ds)
    (e1a : γ1 p1 = γs cs) (e1b : γ1 q1 = γr ar)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0, ‖f (γ0 t) * γ0' t‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1, ‖f (γ1 t) * γ1' t‖ ≤ C1)
    (hmu : mu ≤ ‖∫ t in cs..ds, f (γs t) * γs' t‖)
    (htau : C0 * |q0 - p0| + C1 * |q1 - p1| < mu) :
    ∃ eps : ℂ,
      (∫ t in ar..br, f (γr t) * γr' t)
          = (∫ t in cs..ds, f (γs t) * γs' t) * (1 + eps)
      ∧ ‖eps‖ ≤ (C0 * |q0 - p0| + C1 * |q1 - p1|) / mu
      ∧ ‖eps‖ < 1
      ∧ (∫ t in ar..br, f (γr t) * γr' t) ≠ 0 := by
  have hclose := connector_bound hγr hγs hγ0 hγ1 hgr hgs hg0 hg1
    hir his hi0 hi1 e0a e0b e1a e1b hb0 hb1
  exact LogTransfer.exists_relative_error hclose hmu htau

/-- **SD-C3 → SD-C4 pipeline from holomorphy on a disk (headline).** -/
theorem connector_relative_error_of_holomorphic
    {f : ℂ → ℂ} {ctr : ℂ} {rad : ℝ}
    {γr γr' : ℝ → ℂ} {ar br : ℝ}
    {γs γs' : ℝ → ℂ} {cs ds : ℝ}
    {γ0 γ0' : ℝ → ℂ} {p0 q0 : ℝ}
    {γ1 γ1' : ℝ → ℂ} {p1 q1 : ℝ}
    {C0 C1 mu : ℝ}
    (hf : DifferentiableOn ℂ f (ball ctr rad))
    (hγr : ∀ t ∈ Set.uIcc ar br, HasDerivAt γr (γr' t) t)
    (hγs : ∀ t ∈ Set.uIcc cs ds, HasDerivAt γs (γs' t) t)
    (hγ0 : ∀ t ∈ Set.uIcc p0 q0, HasDerivAt γ0 (γ0' t) t)
    (hγ1 : ∀ t ∈ Set.uIcc p1 q1, HasDerivAt γ1 (γ1' t) t)
    (himr : ∀ t ∈ Set.uIcc ar br, γr t ∈ ball ctr rad)
    (hims : ∀ t ∈ Set.uIcc cs ds, γs t ∈ ball ctr rad)
    (him0 : ∀ t ∈ Set.uIcc p0 q0, γ0 t ∈ ball ctr rad)
    (him1 : ∀ t ∈ Set.uIcc p1 q1, γ1 t ∈ ball ctr rad)
    (hir : IntervalIntegrable (fun t => f (γr t) * γr' t) volume ar br)
    (his : IntervalIntegrable (fun t => f (γs t) * γs' t) volume cs ds)
    (hi0 : IntervalIntegrable (fun t => f (γ0 t) * γ0' t) volume p0 q0)
    (hi1 : IntervalIntegrable (fun t => f (γ1 t) * γ1' t) volume p1 q1)
    (e0a : γ0 p0 = γr br) (e0b : γ0 q0 = γs ds)
    (e1a : γ1 p1 = γs cs) (e1b : γ1 q1 = γr ar)
    (hb0 : ∀ t ∈ Set.uIoc p0 q0, ‖f (γ0 t) * γ0' t‖ ≤ C0)
    (hb1 : ∀ t ∈ Set.uIoc p1 q1, ‖f (γ1 t) * γ1' t‖ ≤ C1)
    (hmu : mu ≤ ‖∫ t in cs..ds, f (γs t) * γs' t‖)
    (htau : C0 * |q0 - p0| + C1 * |q1 - p1| < mu) :
    ∃ eps : ℂ,
      (∫ t in ar..br, f (γr t) * γr' t)
          = (∫ t in cs..ds, f (γs t) * γs' t) * (1 + eps)
      ∧ ‖eps‖ ≤ (C0 * |q0 - p0| + C1 * |q1 - p1|) / mu
      ∧ ‖eps‖ < 1
      ∧ (∫ t in ar..br, f (γr t) * γr' t) ≠ 0 := by
  have hclose := connector_bound_of_holomorphic hf hγr hγs hγ0 hγ1
    himr hims him0 him1 hir his hi0 hi1 e0a e0b e1a e1b hb0 hb1
  exact LogTransfer.exists_relative_error hclose hmu htau

end ContourLegality
end JensenLadder
