import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Resolution wall consumer algebra

This module records the candidate-neutral algebraic half of the Resolution Wall:
a non-adaptive certificate floor bounded below by a fixed positive scale cannot
strictly certify packet margins that are arbitrarily small.

The analytic half of the Resolution Wall -- Paley-Wiener plus Bernstein's
inequality for entire functions of exponential type -- is not formalized here.
It remains a paper `[PROVED-NOTE]` in `docs/rh/resolution_wall_no_go.md`.

## Honest scope

This proves only the deterministic floor-vs-margin obstruction. It does not
prove the Riemann Hypothesis, Paley-Wiener, Bernstein's inequality, or any
packet-to-prime theorem. Theorem M is proven, but Theorem M does not prove RH by
itself.
-/

namespace JensenLadder
namespace ResolutionWall

/-- Any strict certificate margin whose residual cost is nonnegative forces the
additive floor to be strictly below the packet margin. -/
theorem floor_lt_margin_of_certificate_margin
    {cost MB Efloor : ℝ}
    (hcost_nonneg : 0 ≤ cost)
    (hmargin : cost + Efloor < MB) :
    Efloor < MB := by
  linarith

/-- If the additive floor is at least the packet margin, no certificate with
nonnegative residual cost can have a strict margin. -/
theorem certificate_margin_impossible_of_floor_ge_margin
    {cost MB Efloor : ℝ}
    (hcost_nonneg : 0 ≤ cost)
    (hfloor : MB ≤ Efloor) :
    ¬ cost + Efloor < MB := by
  intro hmargin
  have hfloor_lt : Efloor < MB :=
    floor_lt_margin_of_certificate_margin hcost_nonneg hmargin
  linarith

/-- A family of arbitrarily small positive margins contains an index at which a
uniformly positive non-adaptive floor blocks every valid certificate whose
residual cost is nonnegative. -/
theorem exists_margin_index_impossible_of_arbitrarily_small_margins
    {ι Cert : Type*} {MB Efloor : ι → ℝ} {Valid : ι → Cert → Prop}
    {cost : ι → Cert → ℝ} {E0 : ℝ}
    (hE0_pos : 0 < E0)
    (hfloor_lb : ∀ i : ι, E0 ≤ Efloor i)
    (hcost_nonneg : ∀ i c, Valid i c → 0 ≤ cost i c)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ i : ι, 0 < MB i ∧ MB i ≤ eps) :
    ∃ i : ι, 0 < MB i ∧
      ∀ c : Cert, Valid i c → ¬ cost i c + Efloor i < MB i := by
  rcases hsmall E0 hE0_pos with ⟨i, hMB_pos, hMB_le_E0⟩
  refine ⟨i, hMB_pos, ?_⟩
  intro c hvalid
  have hMB_le_floor : MB i ≤ Efloor i := le_trans hMB_le_E0 (hfloor_lb i)
  exact certificate_margin_impossible_of_floor_ge_margin
    (hcost_nonneg i c hvalid) hMB_le_floor

/-- No uniform-floor certificate family can strictly certify every margin index
when valid certificates have nonnegative residual cost and the positive margins
are arbitrarily small. -/
theorem not_forall_certificate_margin_of_uniform_floor_arbitrarily_small_margins
    {ι Cert : Type*} {MB Efloor : ι → ℝ} {Valid : ι → Cert → Prop}
    {cost : ι → Cert → ℝ} {E0 : ℝ}
    (hE0_pos : 0 < E0)
    (hfloor_lb : ∀ i : ι, E0 ≤ Efloor i)
    (hcost_nonneg : ∀ i c, Valid i c → 0 ≤ cost i c)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ i : ι, 0 < MB i ∧ MB i ≤ eps) :
    ¬ ∀ i : ι, ∃ c : Cert, Valid i c ∧ cost i c + Efloor i < MB i := by
  intro hcert
  rcases exists_margin_index_impossible_of_arbitrarily_small_margins
      hE0_pos hfloor_lb hcost_nonneg hsmall with ⟨i, _hMB_pos, hno⟩
  rcases hcert i with ⟨c, hvalid, hmargin⟩
  exact (hno c hvalid) hmargin

end ResolutionWall
end JensenLadder
