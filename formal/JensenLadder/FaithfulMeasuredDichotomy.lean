import Mathlib

/-!
# Stage-0 two-piece reduction: faithful (integer boundary) vs measured (type-II density)

Stage 0 of `docs/plans/program_T3_T5_self_product_construction_20260617.md` (§4.3 first-stone) asks for
the semifinite-Lefschetz-package axioms and the **two-piece reduction**: Weil positivity = a *measured*
bulk piece (type-II / normalized trace, density) **plus** a *faithful* type-I/APS boundary integer
(`κ₋ = 0`). The plan's load-bearing design rationale (lines 28, 47) is that a **normalized type-II trace
is dust-blind** — it sees at most density-1-on-line — so the faithful boundary integer is indispensable.

This file formalizes that rationale, RH-free. We model the inertia data of the finite Weil truncations as
a `WeilInertiaSeq` (`nNeg N` = off-line/negative directions at grid size `N`, among `dim N`), define
**measured** positivity (density `nNeg/dim → 0`) and **faithful** positivity (`nNeg = 0` eventually), and
prove:

* `faithful_imp_measured` — faithful ⟹ measured (the easy direction);
* `measured_not_imp_faithful` — measured does **not** imply faithful: a sequence with exactly one off-line
  direction at every truncation is measured-positive (density `1/(N+1) → 0`) yet never faithful. This is
  the **dust-blindness theorem** — the normalized type-II trace cannot detect bounded off-line dust.

Together they make precise that **Weil positivity is the faithful notion, strictly stronger than the
measured/type-II shadow** — which is exactly why the Stage-0 package needs both a continuous bulk *and* a
faithful boundary integer (not pure normalized II₁). The remaining hard step — that the *arithmetic* Weil
form is faithful-positive (`nNeg = 0`) — is the open RH core (Stage 5), not addressed here.
-/

open Filter Topology

namespace JensenLadder

/-- A **Weil inertia sequence**: at truncation `N`, `nNeg N` off-line (negative) directions of the finite
Weil form, among `dim N` total. The off-line count is the faithful boundary integer; its density is what a
normalized type-II trace sees. -/
structure WeilInertiaSeq where
  nNeg : ℕ → ℕ
  dim : ℕ → ℕ
  dim_pos : ∀ N, 0 < dim N

/-- **Measured positivity** (type-II / normalized-trace view): the *density* of off-line directions → 0.
The "dust-blind" notion — the most a normalized II₁ trace can certify. -/
def WeilInertiaSeq.MeasuredPositive (S : WeilInertiaSeq) : Prop :=
  Tendsto (fun N => (S.nNeg N : ℝ) / (S.dim N : ℝ)) atTop (𝓝 0)

/-- **Faithful positivity** (type-I/APS faithful boundary integer = 0 eventually): genuinely no off-line
direction. This is `κ₋ = 0`, the Weil-positivity notion. -/
def WeilInertiaSeq.FaithfulPositive (S : WeilInertiaSeq) : Prop :=
  ∀ᶠ N in atTop, S.nNeg N = 0

/-- **Faithful ⟹ measured** (the easy direction): a vanishing faithful boundary integer forces the
type-II density to vanish. -/
theorem faithful_imp_measured (S : WeilInertiaSeq) (h : S.FaithfulPositive) :
    S.MeasuredPositive := by
  refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
  filter_upwards [h] with N hN
  simp [hN]

/-- **Measured does NOT imply faithful — the dust-blindness theorem.** There is a Weil inertia sequence
with exactly one off-line direction at every truncation: it is measured-positive (density `1/(N+1) → 0`)
yet never faithful-positive. Hence a normalized type-II trace is blind to bounded off-line "dust", and the
faithful (type-I/APS) boundary integer is indispensable — the Stage-0 rationale (plan lines 28, 47) as a
theorem. -/
theorem measured_not_imp_faithful :
    ∃ S : WeilInertiaSeq, S.MeasuredPositive ∧ ¬ S.FaithfulPositive := by
  refine ⟨⟨fun _ => 1, fun N => N + 1, fun N => Nat.succ_pos N⟩, ?_, ?_⟩
  · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hgoal : Tendsto (fun N : ℕ => ((1 : ℕ) : ℝ) / (((N + 1 : ℕ)) : ℝ)) atTop (𝓝 0) := by
      refine h0.congr' ?_
      filter_upwards with N
      push_cast; ring
    exact hgoal
  · intro h
    obtain ⟨N, hN⟩ := h.exists
    exact one_ne_zero hN

end JensenLadder
