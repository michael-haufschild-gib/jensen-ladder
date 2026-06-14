import Mathlib.Tactic

/-!
# Burnol critical complete/minimal systems

This module records the formal shape extracted from Burnol's zero-indexed
systems:

```text
  complete iff a >= 1,
  minimal  iff a <= 1.
```

Thus complete+minimal occurs exactly at the critical threshold `a = 1`.  This
is a no-margin diagnostic, not a determinant-class theorem.  In particular,
complete+minimal exactness does not by itself provide a Riesz basis,
trace-class control, Hilbert--Schmidt control, or the Fork-A determinant rows.

The file is only an abstract calibration of the threshold logic.  It does not
formalize Burnol's analytic proof, Meyer's operator, Schatten-class estimates,
or RH.  Evidence class: formal/certificate artifact and dead-end elimination.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace BurnolCriticalSystems

universe u

/--
A family of Hilbert-space systems with a complete/minimal threshold.

`complete_iff` and `minimal_iff` encode the Burnol pattern abstractly: at and
above the critical scale the system is complete; at and below it the system is
minimal.
-/
structure CriticalCompleteMinimalFamily (α : Type u) [LinearOrder α] where
  critical : α
  complete : α -> Prop
  minimal : α -> Prop
  complete_iff : ∀ a : α, complete a ↔ critical <= a
  minimal_iff : ∀ a : α, minimal a ↔ a <= critical

namespace CriticalCompleteMinimalFamily

variable {α : Type u} [LinearOrder α]

/-- Complete and minimal at the same scale. -/
def Exact (F : CriticalCompleteMinimalFamily α) (a : α) : Prop :=
  F.complete a ∧ F.minimal a

/-- In a threshold family, exactness occurs exactly at the critical scale. -/
theorem exact_iff_eq_critical
    (F : CriticalCompleteMinimalFamily α) (a : α) :
    F.Exact a ↔ a = F.critical := by
  constructor
  · intro h
    exact le_antisymm ((F.minimal_iff a).1 h.2)
      ((F.complete_iff a).1 h.1)
  · intro ha
    subst ha
    exact ⟨(F.complete_iff F.critical).2 le_rfl,
      (F.minimal_iff F.critical).2 le_rfl⟩

/-- Below the critical scale, completeness fails. -/
theorem not_complete_of_lt_critical
    (F : CriticalCompleteMinimalFamily α) {a : α}
    (ha : a < F.critical) :
    ¬ F.complete a := by
  intro hcomplete
  exact (not_le_of_gt ha) ((F.complete_iff a).1 hcomplete)

/-- Above the critical scale, minimality fails. -/
theorem not_minimal_of_critical_lt
    (F : CriticalCompleteMinimalFamily α) {a : α}
    (ha : F.critical < a) :
    ¬ F.minimal a := by
  intro hminimal
  exact (not_le_of_gt ha) ((F.minimal_iff a).1 hminimal)

/-- Below the critical scale, exactness fails because completeness fails. -/
theorem not_exact_of_lt_critical
    (F : CriticalCompleteMinimalFamily α) {a : α}
    (ha : a < F.critical) :
    ¬ F.Exact a := by
  intro hexact
  exact F.not_complete_of_lt_critical ha hexact.1

/-- Above the critical scale, exactness fails because minimality fails. -/
theorem not_exact_of_critical_lt
    (F : CriticalCompleteMinimalFamily α) {a : α}
    (ha : F.critical < a) :
    ¬ F.Exact a := by
  intro hexact
  exact F.not_minimal_of_critical_lt ha hexact.2

end CriticalCompleteMinimalFamily

/-- The abstract Burnol threshold on real scales, with critical point `1`. -/
def burnolThresholdFamily : CriticalCompleteMinimalFamily ℝ where
  critical := 1
  complete := fun a => 1 <= a
  minimal := fun a => a <= 1
  complete_iff := by
    intro a
    rfl
  minimal_iff := by
    intro a
    rfl

namespace burnolThresholdFamily

/-- The Burnol threshold is exact exactly at `a = 1`. -/
theorem exact_iff_eq_one (a : ℝ) :
    burnolThresholdFamily.Exact a ↔ a = 1 :=
  burnolThresholdFamily.exact_iff_eq_critical a

/-- At `a = 1`, the threshold family is both complete and minimal. -/
theorem exact_one :
    burnolThresholdFamily.Exact 1 :=
  (exact_iff_eq_one 1).2 rfl

/--
The critical exactness has no two-sided open margin: moving any positive amount
left loses completeness, and moving any positive amount right loses minimality.
-/
theorem no_two_sided_exact_margin {ε : ℝ}
    (hε : 0 < ε) :
    ¬ burnolThresholdFamily.Exact (1 - ε) ∧
      ¬ burnolThresholdFamily.Exact (1 + ε) := by
  constructor
  · exact burnolThresholdFamily.not_exact_of_lt_critical (by
      dsimp [burnolThresholdFamily]
      linarith)
  · exact burnolThresholdFamily.not_exact_of_critical_lt (by
      dsimp [burnolThresholdFamily]
      linarith)

end burnolThresholdFamily

/--
A threshold family decorated with stronger analytic rows.

The extra rows are intentionally independent of complete/minimal exactness:
complete+minimal systems need not be Riesz bases, and neither Riesz rows nor
determinant-class rows are supplied by threshold exactness alone.
-/
structure DecoratedCriticalFamily (α : Type u) [LinearOrder α] extends
    CriticalCompleteMinimalFamily α where
  rieszBasis : α -> Prop
  determinantClass : α -> Prop

namespace DecoratedCriticalFamily

variable {α : Type u} [LinearOrder α]

/-- Exactness for the underlying threshold family. -/
def Exact (F : DecoratedCriticalFamily α) (a : α) : Prop :=
  F.toCriticalCompleteMinimalFamily.Exact a

end DecoratedCriticalFamily

/--
A Burnol-shaped dummy family where complete+minimal exactness holds at the
critical scale but the Riesz and determinant-class rows are absent.
-/
def nonRieszBurnolFamily : DecoratedCriticalFamily ℝ where
  critical := 1
  complete := fun a => 1 <= a
  minimal := fun a => a <= 1
  complete_iff := by
    intro a
    rfl
  minimal_iff := by
    intro a
    rfl
  rieszBasis := fun _ => False
  determinantClass := fun _ => False

/-- Complete+minimal exactness at the critical scale does not supply a Riesz basis. -/
theorem exactCriticalRows_do_not_supply_rieszBasis :
    ∃ F : DecoratedCriticalFamily ℝ,
      F.Exact F.critical ∧ ¬ F.rieszBasis F.critical := by
  refine ⟨nonRieszBurnolFamily, ?_, ?_⟩
  · exact burnolThresholdFamily.exact_one
  · intro h
    exact h

/--
Complete+minimal exactness at the critical scale does not supply determinant
class control.
-/
theorem exactCriticalRows_do_not_supply_determinantClass :
    ∃ F : DecoratedCriticalFamily ℝ,
      F.Exact F.critical ∧ ¬ F.determinantClass F.critical := by
  refine ⟨nonRieszBurnolFamily, ?_, ?_⟩
  · exact burnolThresholdFamily.exact_one
  · intro h
    exact h

end BurnolCriticalSystems
end JensenLadder
