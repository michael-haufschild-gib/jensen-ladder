import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# E1K deterministic contraction core

This file starts the Lean formalization of the E1K shifted-saddle certificate
used in the RH workspace notes.  It contains the deterministic metric core:
a contraction mapping a closed ball into itself has a unique fixed point in
that ball, a Lipschitz phase observable transfers distance error to phase
error, and the complex division algebra for the shifted-saddle map
`delta ↦ -ell / A delta`.
-/

namespace JensenLadder
namespace E1K

open Function Metric Set

variable {α : Type*} [MetricSpace α]

/--
Any two fixed points of a contraction on a closed ball are equal.

This is factored out because the unique fixed point constructed by
`exists_fixedPoint_closedBall` is often not the object named in later
certificate calculations.
-/
theorem fixedPoint_unique_closedBall
    {center : α} {r : ℝ} {K : NNReal} {T : α → α}
    (hK : K < 1)
    (hmap : MapsTo T (closedBall center r) (closedBall center r))
    (hLip :
      ∀ ⦃x⦄, x ∈ closedBall center r →
      ∀ ⦃y⦄, y ∈ closedBall center r →
        dist (T x) (T y) ≤ (K : ℝ) * dist x y)
    {x y : α}
    (hxmem : x ∈ closedBall center r) (hymem : y ∈ closedBall center r)
    (hx : T x = x) (hy : T y = y) :
    x = y := by
  let s : Set α := closedBall center r
  have hcontract : ContractingWith K (hmap.restrict T s s) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    exact hLip u.property v.property
  have hx' : IsFixedPt (hmap.restrict T s s) ⟨x, hxmem⟩ := by
    ext
    exact hx
  have hy' : IsFixedPt (hmap.restrict T s s) ⟨y, hymem⟩ := by
    ext
    exact hy
  exact Subtype.ext_iff.mp (hcontract.fixedPoint_unique' hx' hy')

/--
Closed-ball Banach certificate.

If `T` maps `closedBall center r` into itself and is contracting there, then
there is a fixed point in the closed ball, unique among fixed points in that
closed ball.
-/
theorem exists_fixedPoint_closedBall
    [CompleteSpace α]
    {center : α} {r : ℝ} {K : NNReal} {T : α → α}
    (hK : K < 1)
    (hmap : MapsTo T (closedBall center r) (closedBall center r))
    (hLip :
      ∀ ⦃x⦄, x ∈ closedBall center r →
      ∀ ⦃y⦄, y ∈ closedBall center r →
        dist (T x) (T y) ≤ (K : ℝ) * dist x y)
    {x0 : α} (hx0 : x0 ∈ closedBall center r) :
    ∃ x ∈ closedBall center r,
      T x = x ∧
      ∀ ⦃y⦄, y ∈ closedBall center r → T y = y → y = x := by
  let s : Set α := closedBall center r
  have hs_closed : IsClosed s := isClosed_closedBall
  have hs_complete : IsComplete s := hs_closed.isComplete
  have hcontract : ContractingWith K (hmap.restrict T s s) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hLip x.property y.property
  have hx_edist : edist x0 (T x0) ≠ ⊤ := edist_ne_top _ _
  rcases hcontract.exists_fixedPoint' hs_complete hmap hx0 hx_edist with
    ⟨x, hxmem, hfixed, _htendsto, _hbound⟩
  refine ⟨x, hxmem, hfixed.eq, ?_⟩
  intro y hymem hyfixed
  exact fixedPoint_unique_closedBall hK hmap hLip hymem hxmem hyfixed hfixed.eq

/--
Phase-observable error transfer: if `P` is `P1`-Lipschitz between two
certificate points and the points are within `eps`, then the phase values are
within `P1 * eps`.
-/
theorem phase_error_le
    {P : α → ℝ} {x y : α} {P1 eps : ℝ}
    (hP : |P x - P y| ≤ P1 * dist x y)
    (hxy : dist x y ≤ eps)
    (hP1 : 0 ≤ P1) :
    |P x - P y| ≤ P1 * eps := by
  exact hP.trans (mul_le_mul_of_nonneg_left hxy hP1)

/--
The shifted-saddle map sends the closed delta ball into itself when the
forcing term is bounded by `m`, the denominator is bounded below by `a`, and
`m / a` fits inside the radius.
-/
theorem shiftedSaddle_mapsTo_closedBall
    {r m a : ℝ} {ell : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (ha : 0 < a)
    (hA : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → a ≤ ‖A δ‖)
    (hr : m / a ≤ r) :
    MapsTo (fun δ : ℂ => -ell / A δ) (closedBall (0 : ℂ) r) (closedBall (0 : ℂ) r) := by
  intro δ hδ
  rw [mem_closedBall]
  rw [dist_eq_norm]
  simp only [sub_zero]
  have hAδ : a ≤ ‖A δ‖ := hA hδ
  have hnorm : ‖-ell / A δ‖ = ‖ell‖ / ‖A δ‖ := by
    rw [Complex.norm_div, norm_neg]
  calc
    ‖-ell / A δ‖ = ‖ell‖ / ‖A δ‖ := hnorm
    _ ≤ ‖ell‖ / a := div_le_div_of_nonneg_left (norm_nonneg ell) ha hAδ
    _ ≤ m / a := div_le_div_of_nonneg_right hell ha.le
    _ ≤ r := hr

/--
Algebraic Lipschitz estimate for the shifted-saddle map
`delta ↦ -ell / A delta`.

If `A` is bounded below by `a` on the closed ball and has Lipschitz constant
`b` there, then the shifted-saddle map has Lipschitz constant
`m * b / a^2`.
-/
theorem shiftedSaddle_dist_le_closedBall
    {r m a b : ℝ} {ell : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (ha : 0 < a)
    (hA : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → a ≤ ‖A δ‖)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ b * dist δ ε) :
    ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
    ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
      dist (-ell / A δ) (-ell / A ε) ≤ (m * b / a ^ 2) * dist δ ε := by
  intro δ hδ ε hε
  have hAδ : a ≤ ‖A δ‖ := hA hδ
  have hAε : a ≤ ‖A ε‖ := hA hε
  have hAδ_pos : 0 < ‖A δ‖ := lt_of_lt_of_le ha hAδ
  have hAε_pos : 0 < ‖A ε‖ := lt_of_lt_of_le ha hAε
  have hAδ_ne : A δ ≠ 0 := norm_pos_iff.mp hAδ_pos
  have hAε_ne : A ε ≠ 0 := norm_pos_iff.mp hAε_pos
  have hden_lower : a ^ 2 ≤ ‖A δ‖ * ‖A ε‖ := by
    have hmul : a * a ≤ ‖A δ‖ * ‖A ε‖ :=
      mul_le_mul hAδ hAε ha.le (norm_nonneg (A δ))
    simpa [sq] using hmul
  have hnum_nonneg : 0 ≤ ‖ell‖ * ‖A δ - A ε‖ :=
    mul_nonneg (norm_nonneg ell) (norm_nonneg (A δ - A ε))
  have hnum_le : ‖ell‖ * ‖A δ - A ε‖ ≤ m * (b * dist δ ε) := by
    exact mul_le_mul hell (hLipA hδ hε) (norm_nonneg (A δ - A ε)) hm
  have hsub : -ell / A δ - -ell / A ε = ell * (A δ - A ε) / (A δ * A ε) := by
    rw [div_sub_div (-ell) (-ell) hAδ_ne hAε_ne]
    field_simp [hAδ_ne, hAε_ne]
    ring
  calc
    dist (-ell / A δ) (-ell / A ε)
        = ‖ell‖ * ‖A δ - A ε‖ / (‖A δ‖ * ‖A ε‖) := by
          rw [dist_eq_norm, hsub, Complex.norm_div, Complex.norm_mul, Complex.norm_mul]
    _ ≤ ‖ell‖ * ‖A δ - A ε‖ / a ^ 2 :=
          div_le_div_of_nonneg_left hnum_nonneg (sq_pos_of_pos ha) hden_lower
    _ ≤ m * (b * dist δ ε) / a ^ 2 :=
          div_le_div_of_nonneg_right hnum_le (sq_pos_of_pos ha).le
    _ = (m * b / a ^ 2) * dist δ ε := by ring

/--
Shifted-saddle fixed-point certificate on the closed delta ball.

This packages the algebraic `m * b / a^2` estimate into the abstract Banach
certificate above.  Later analytic work only has to supply the lower bound on
`A`, the Lipschitz estimate on `A`, and a concrete `K < 1` dominating
`m * b / a^2`.
-/
theorem exists_shiftedSaddle_fixedPoint_closedBall
    {r m a b : ℝ} {K : NNReal} {ell : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (ha : 0 < a)
    (hA : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → a ≤ ‖A δ‖)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ b * dist δ ε)
    (hr : m / a ≤ r)
    (hK : K < 1)
    (hqK : m * b / a ^ 2 ≤ (K : ℝ)) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hmap : MapsTo (fun δ : ℂ => -ell / A δ)
      (closedBall (0 : ℂ) r) (closedBall (0 : ℂ) r) :=
    shiftedSaddle_mapsTo_closedBall hell ha hA hr
  have hLip0 := shiftedSaddle_dist_le_closedBall hell hm ha hA hLipA
  have hLip :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        dist ((fun z : ℂ => -ell / A z) δ) ((fun z : ℂ => -ell / A z) ε) ≤
          (K : ℝ) * dist δ ε := by
    intro δ hδ ε hε
    calc
      dist (-ell / A δ) (-ell / A ε) ≤ (m * b / a ^ 2) * dist δ ε := hLip0 hδ hε
      _ ≤ (K : ℝ) * dist δ ε := mul_le_mul_of_nonneg_right hqK dist_nonneg
  have hr_nonneg : 0 ≤ r := by
    exact (div_nonneg hm ha.le).trans hr
  exact exists_fixedPoint_closedBall hK hmap hLip (mem_closedBall_self hr_nonneg)

/--
Shifted-saddle fixed-point certificate using the natural real contraction
gate `m * b / a^2 < 1`.

This is the certificate-facing version of
`exists_shiftedSaddle_fixedPoint_closedBall`: it constructs the `NNReal`
contraction constant internally.
-/
theorem exists_shiftedSaddle_fixedPoint_closedBall_of_real_contraction
    {r m a b : ℝ} {ell : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hb : 0 ≤ b)
    (ha : 0 < a)
    (hA : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → a ≤ ‖A δ‖)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ b * dist δ ε)
    (hr : m / a ≤ r)
    (hq : m * b / a ^ 2 < 1) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hq_nonneg : 0 ≤ m * b / a ^ 2 :=
    div_nonneg (mul_nonneg hm hb) (sq_pos_of_pos ha).le
  let K : NNReal := ⟨m * b / a ^ 2, hq_nonneg⟩
  have hK : K < 1 := by
    exact (Subtype.mk_lt_mk).mpr hq
  have hqK : m * b / a ^ 2 ≤ (K : ℝ) := le_rfl
  exact exists_shiftedSaddle_fixedPoint_closedBall hell hm ha hA hLipA hr hK hqK

/--
Converts a center approximation `A delta ≈ H` into the denominator lower
bound needed by the shifted-saddle certificate.

This is the formal version of the gate `a <= |H| - err`.
-/
theorem denominator_lower_of_center_error_closedBall
    {r a err : ℝ} {H : ℂ} {A : ℂ → ℂ}
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ err)
    (ha : a ≤ ‖H‖ - err) :
    ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → a ≤ ‖A δ‖ := by
  intro δ hδ
  have hdiff : ‖H‖ - ‖A δ‖ ≤ err := by
    calc
      ‖H‖ - ‖A δ‖ ≤ ‖H - A δ‖ := norm_sub_norm_le H (A δ)
      _ = ‖A δ - H‖ := norm_sub_rev H (A δ)
      _ ≤ err := hcenter hδ
  have hlower : ‖H‖ - err ≤ ‖A δ‖ := by
    rw [sub_le_iff_le_add']
    rw [sub_le_iff_le_add] at hdiff
    simpa [add_comm] using hdiff
  exact ha.trans hlower

/--
Shifted-saddle fixed-point certificate using a center-error bound for `A`.

Analytic or numerical certificates may supply `‖A delta - H‖ <= err` and
`a <= ‖H‖ - err`, instead of proving the denominator lower bound directly.
-/
theorem exists_shiftedSaddle_fixedPoint_of_center_error_closedBall
    {r m a b err : ℝ} {K : NNReal} {ell H : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ err)
    (ha_lower : a ≤ ‖H‖ - err)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ b * dist δ ε)
    (hr : m / a ≤ r)
    (hK : K < 1)
    (hqK : m * b / a ^ 2 ≤ (K : ℝ)) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  exact exists_shiftedSaddle_fixedPoint_closedBall hell hm ha_pos
    (denominator_lower_of_center_error_closedBall hcenter ha_lower) hLipA hr hK hqK

/--
Center-error shifted-saddle certificate using the natural real contraction
gate `m * b / a^2 < 1`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_center_error_real_contraction
    {r m a b err : ℝ} {ell H : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hb : 0 ≤ b)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ err)
    (ha_lower : a ≤ ‖H‖ - err)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ b * dist δ ε)
    (hr : m / a ≤ r)
    (hq : m * b / a ^ 2 < 1) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  exact exists_shiftedSaddle_fixedPoint_closedBall_of_real_contraction hell hm hb ha_pos
    (denominator_lower_of_center_error_closedBall hcenter ha_lower) hLipA hr hq

/--
Derivative-supremum E1K certificate.

This is the F271-style consumer contract: a single derivative supremum `h1`
controls both the center error `h1 * r / 2` and the Lipschitz constant
`h1 / 2`.  The contraction gate is the corresponding real inequality
`m * h1 / (2 * a^2) < 1`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction
    {r m a h1 : ℝ} {ell H : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hh1 : 0 ≤ h1)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ h1 * r / 2)
    (ha_lower : a ≤ ‖H‖ - h1 * r / 2)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ (h1 / 2) * dist δ ε)
    (hr : m / a ≤ r)
    (hq : m * h1 / (2 * a ^ 2) < 1) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hb : 0 ≤ h1 / 2 := div_nonneg hh1 (by norm_num)
  have hq' : m * (h1 / 2) / a ^ 2 < 1 := by
    calc
      m * (h1 / 2) / a ^ 2 = m * h1 / (2 * a ^ 2) := by ring
      _ < 1 := hq
  exact exists_shiftedSaddle_fixedPoint_of_center_error_real_contraction hell hm hb ha_pos
    hcenter ha_lower hLipA hr hq'

/--
Distance from a shifted-saddle fixed point to the first approximation
`delta0 = -ell / H`.

When `H = A 0`, the contraction estimate and the fixed-point equation give
the deterministic E1K bound
`dist delta delta0 <= (m * b / a^2) * (m / a)`.
-/
theorem shiftedSaddle_fixedPoint_dist_approx_le
    {r m a b : ℝ} {ell H δ : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hb : 0 ≤ b)
    (ha : 0 < a)
    (hA : ∀ ⦃ζ⦄, ζ ∈ closedBall (0 : ℂ) r → a ≤ ‖A ζ‖)
    (hLipA :
      ∀ ⦃ζ⦄, ζ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃η⦄, η ∈ closedBall (0 : ℂ) r →
        ‖A ζ - A η‖ ≤ b * dist ζ η)
    (hδmem : δ ∈ closedBall (0 : ℂ) r)
    (h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) r)
    (hA0 : A 0 = H)
    (hfixed : -ell / A δ = δ) :
    dist δ (-ell / H) ≤ (m * b / a ^ 2) * (m / a) := by
  have hLip0 := shiftedSaddle_dist_le_closedBall hell hm ha hA hLipA hδmem h0mem
  have hq_nonneg : 0 ≤ m * b / a ^ 2 :=
    div_nonneg (mul_nonneg hm hb) (sq_pos_of_pos ha).le
  have hAδ : a ≤ ‖A δ‖ := hA hδmem
  have hdist0 : dist δ 0 ≤ m / a := by
    rw [dist_eq_norm, sub_zero]
    rw [← hfixed]
    calc
      ‖-ell / A δ‖ = ‖ell‖ / ‖A δ‖ := by
        rw [Complex.norm_div, norm_neg]
      _ ≤ ‖ell‖ / a := div_le_div_of_nonneg_left (norm_nonneg ell) ha hAδ
      _ ≤ m / a := div_le_div_of_nonneg_right hell ha.le
  have happrox : -ell / H = -ell / A 0 := by
    rw [hA0]
  calc
    dist δ (-ell / H) = dist (-ell / A δ) (-ell / A 0) := by
      nth_rewrite 1 [← hfixed]
      rw [happrox]
    _ ≤ (m * b / a ^ 2) * dist δ 0 := hLip0
    _ ≤ (m * b / a ^ 2) * (m / a) :=
      mul_le_mul_of_nonneg_left hdist0 hq_nonneg

/--
Derivative-supremum E1K certificate including the first-approximation error
bound `dist delta (-ell/H) <= q * m/a`, with `q = m*(h1/2)/a^2`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_error
    {r m a h1 : ℝ} {ell H : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hh1 : 0 ≤ h1)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ h1 * r / 2)
    (ha_lower : a ≤ ‖H‖ - h1 * r / 2)
    (hA0 : A 0 = H)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ (h1 / 2) * dist δ ε)
    (hr : m / a ≤ r)
    (hq : m * h1 / (2 * a ^ 2) < 1) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      dist δ (-ell / H) ≤ (m * (h1 / 2) / a ^ 2) * (m / a) ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hb : 0 ≤ h1 / 2 := div_nonneg hh1 (by norm_num)
  have hq' : m * (h1 / 2) / a ^ 2 < 1 := by
    calc
      m * (h1 / 2) / a ^ 2 = m * h1 / (2 * a ^ 2) := by ring
      _ < 1 := hq
  rcases exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction
      hell hm hh1 ha_pos hcenter ha_lower hLipA hr hq with
    ⟨δ, hδmem, hfixed, huniq⟩
  have hA : ∀ ⦃ζ⦄, ζ ∈ closedBall (0 : ℂ) r → a ≤ ‖A ζ‖ :=
    denominator_lower_of_center_error_closedBall hcenter ha_lower
  have hr_nonneg : 0 ≤ r := by
    exact (div_nonneg hm ha_pos.le).trans hr
  have herr : dist δ (-ell / H) ≤ (m * (h1 / 2) / a ^ 2) * (m / a) :=
    shiftedSaddle_fixedPoint_dist_approx_le hell hm hb ha_pos hA hLipA hδmem
      (mem_closedBall_self hr_nonneg) hA0 hfixed
  exact ⟨δ, hδmem, hfixed, herr, huniq⟩

/--
Derivative-supremum E1K certificate including a phase-observable error bound.

This packages the deterministic E1K endpoint used by the finite-d T1 table:
once `P` is `P1`-Lipschitz from the fixed point to
`delta0 = -ell / H`, the phase error is bounded by `P1 * q * m/a`, with
`q = m*(h1/2)/a^2`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_phase_error
    {r m a h1 P1 : ℝ} {ell H : ℂ} {A : ℂ → ℂ} {P : ℂ → ℝ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hh1 : 0 ≤ h1)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ h1 * r / 2)
    (ha_lower : a ≤ ‖H‖ - h1 * r / 2)
    (hA0 : A 0 = H)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ (h1 / 2) * dist δ ε)
    (hr : m / a ≤ r)
    (hq : m * h1 / (2 * a ^ 2) < 1)
    (hP1 : 0 ≤ P1)
    (hP : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      |P δ - P (-ell / H)| ≤ P1 * dist δ (-ell / H)) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      |P δ - P (-ell / H)| ≤ P1 * ((m * (h1 / 2) / a ^ 2) * (m / a)) ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  rcases exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_error
      hell hm hh1 ha_pos hcenter ha_lower hA0 hLipA hr hq with
    ⟨δ, hδmem, hfixed, herr, huniq⟩
  have hphase :
      |P δ - P (-ell / H)| ≤ P1 * ((m * (h1 / 2) / a ^ 2) * (m / a)) :=
    phase_error_le (hP hδmem) herr hP1
  exact ⟨δ, hδmem, hfixed, hphase, huniq⟩

/--
Q-explicit derivative-supremum E1K certificate including the
first-approximation error bound.

This wrapper exposes the contraction constant `q` as a table input, while
retaining the checked identity `q = m*h1/(2*a^2)`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_error_q
    {r m a h1 q : ℝ} {ell H : ℂ} {A : ℂ → ℂ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hh1 : 0 ≤ h1)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ h1 * r / 2)
    (ha_lower : a ≤ ‖H‖ - h1 * r / 2)
    (hA0 : A 0 = H)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ (h1 / 2) * dist δ ε)
    (hr : m / a ≤ r)
    (hq_def : q = m * h1 / (2 * a ^ 2))
    (hq : q < 1) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      dist δ (-ell / H) ≤ q * (m / a) ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hq' : m * h1 / (2 * a ^ 2) < 1 := by
    rw [← hq_def]
    exact hq
  rcases exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_error
      hell hm hh1 ha_pos hcenter ha_lower hA0 hLipA hr hq' with
    ⟨δ, hδmem, hfixed, herr, huniq⟩
  have herr' : dist δ (-ell / H) ≤ q * (m / a) := by
    calc
      dist δ (-ell / H) ≤ (m * (h1 / 2) / a ^ 2) * (m / a) := herr
      _ = q * (m / a) := by
        rw [hq_def]
        ring
  exact ⟨δ, hδmem, hfixed, herr', huniq⟩

/--
Q-explicit derivative-supremum E1K certificate including a phase-observable
error bound.

This is the finite-table consumer endpoint: a certified `q` row plus a
`P1`-Lipschitz phase observable gives `|P(delta*) - P(delta0)| <= P1*q*m/a`.
-/
theorem exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_phase_error_q
    {r m a h1 q P1 : ℝ} {ell H : ℂ} {A : ℂ → ℂ} {P : ℂ → ℝ}
    (hell : ‖ell‖ ≤ m)
    (hm : 0 ≤ m)
    (hh1 : 0 ≤ h1)
    (ha_pos : 0 < a)
    (hcenter : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r → ‖A δ - H‖ ≤ h1 * r / 2)
    (ha_lower : a ≤ ‖H‖ - h1 * r / 2)
    (hA0 : A 0 = H)
    (hLipA :
      ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r →
        ‖A δ - A ε‖ ≤ (h1 / 2) * dist δ ε)
    (hr : m / a ≤ r)
    (hq_def : q = m * h1 / (2 * a ^ 2))
    (hq : q < 1)
    (hP1 : 0 ≤ P1)
    (hP : ∀ ⦃δ⦄, δ ∈ closedBall (0 : ℂ) r →
      |P δ - P (-ell / H)| ≤ P1 * dist δ (-ell / H)) :
    ∃ δ ∈ closedBall (0 : ℂ) r,
      -ell / A δ = δ ∧
      |P δ - P (-ell / H)| ≤ P1 * (q * (m / a)) ∧
      ∀ ⦃ε⦄, ε ∈ closedBall (0 : ℂ) r → -ell / A ε = ε → ε = δ := by
  have hq' : m * h1 / (2 * a ^ 2) < 1 := by
    rw [← hq_def]
    exact hq
  rcases exists_shiftedSaddle_fixedPoint_of_derivative_sup_real_contraction_with_phase_error
      hell hm hh1 ha_pos hcenter ha_lower hA0 hLipA hr hq' hP1 hP with
    ⟨δ, hδmem, hfixed, hphase, huniq⟩
  have hphase' : |P δ - P (-ell / H)| ≤ P1 * (q * (m / a)) := by
    calc
      |P δ - P (-ell / H)| ≤ P1 * ((m * (h1 / 2) / a ^ 2) * (m / a)) := hphase
      _ = P1 * (q * (m / a)) := by
        rw [hq_def]
        ring
  exact ⟨δ, hδmem, hfixed, hphase', huniq⟩

end E1K
end JensenLadder
