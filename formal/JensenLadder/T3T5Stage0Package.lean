import Mathlib
import JensenLadder.HodgeIndexLorentzian

/-!
# Stage 0 of the T3/T5 program: the d=2 Lefschetz package and its bulk reduction

This formalizes Stage 0 of `docs/plans/program_T3_T5_self_product_construction_20260617.md`
at the finite (degree-2) level: the **Lefschetz-package axioms** plus the **bulk
reduction** "Hodge–Riemann ⟺ Weil/polarized positivity".

The package data (d=2): the degree-1 piece `A₁ = ι → ℝ`, a symmetric **intersection
form** `Q` (the degree-2 pairing `A₁ × A₁ → A₂ ≅ ℝ`), and an **ample/Lefschetz**
vector `L` with `Q(L,L) > 0` (hard Lefschetz `L²: A₀ → A₂` iso reduces, for `d=2`, to
`Q(L,L) ≠ 0`).

- `HodgeRiemann` (bulk): `Q` is negative-semidefinite on the `Q`-orthogonal
  complement `L^⊥` (the primitive part) — the **measured/density** positivity (the
  type-II bulk of the plan's "semifinite Lefschetz package").
- `WeilPSD`: the Lorentzian reverse-Cauchy–Schwarz form `Q(L,x)² − Q(L,L)Q(x,x) ≥ 0`
  — positive-semidefiniteness of the polarized/Weil form.

**Stage-0 reduction (proved here):** `HodgeRiemann ↔ WeilPSD` (the Hodge-index
equivalence, `HodgeIndexLorentzian.hodge_index_iff`).  The strict versions coincide
likewise.  This is the **bulk** (measured) half of the plan's Stage-0 deliverable.

**What is NOT here (honest, per the plan and `rh_faithful_vs_measured_dichotomy`).**
The finite/bulk `HodgeRiemann` is the *measured* (density, dust-blind) positivity.
The plan's full Stage-0 deliverable also needs the **faithful type-I/APS boundary
integer `κ₋`** (every off-line zero, not a density) and `κ₋ = 0`; that is an
infinite-limit refinement (berry's faithful defect `Δ_½ = Σ(Re ρ−½)`), NOT a finite
linear-algebra fact, and is left as the open boundary row.  And `WeilPSD ⟺ RH` is
Weil's criterion in the limit (imported, not proved).  So this module proves the
*finite bulk reduction* exactly; the faithful boundary integer and the limit are the
genuinely-open parts.  Axiom-clean.
-/

namespace JensenLadder
namespace T3T5Stage0

open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- The d=2 Lefschetz-package data: a symmetric intersection form `Q` on `A₁ = ι→ℝ`
with an ample/Lefschetz vector `L` (`Q(L,L) > 0`). -/
structure LefschetzD2 (ι : Type*) [Fintype ι] where
  Q : Matrix ι ι ℝ
  hsymm : Qᵀ = Q
  L : ι → ℝ
  hample : 0 < L ⬝ᵥ Q *ᵥ L

namespace LefschetzD2

variable (P : LefschetzD2 ι)

/-- Hodge–Riemann (bulk / measured): `Q ⪯ 0` on the primitive part `L^⊥`. -/
def HodgeRiemann : Prop :=
  ∀ x : ι → ℝ, P.L ⬝ᵥ P.Q *ᵥ x = 0 → x ⬝ᵥ P.Q *ᵥ x ≤ 0

/-- Strict Hodge–Riemann: `Q ≺ 0` on the *nonzero* primitive part. -/
def HodgeRiemannStrict : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → P.L ⬝ᵥ P.Q *ᵥ x = 0 → x ⬝ᵥ P.Q *ᵥ x < 0

/-- Weil/polarized positivity: the Lorentzian reverse-Cauchy–Schwarz form is `≥ 0`. -/
def WeilPSD : Prop :=
  ∀ x : ι → ℝ, 0 ≤ (P.L ⬝ᵥ P.Q *ᵥ x) ^ 2 - (P.L ⬝ᵥ P.Q *ᵥ P.L) * (x ⬝ᵥ P.Q *ᵥ x)

/-- **Stage-0 bulk reduction:** Hodge–Riemann on `L^⊥` ⟺ Weil/polarized positivity.
This is the packaged Hodge-index equivalence. -/
theorem hodgeRiemann_iff_weilPSD : P.HodgeRiemann ↔ P.WeilPSD :=
  HodgeIndexLorentzian.hodge_index_iff P.Q P.hsymm P.L P.hample

/-- The Weil/reverse-CS inequality holds for every `x` once Hodge–Riemann does. -/
theorem reverseCS_of_hodgeRiemann (h : P.HodgeRiemann) (x : ι → ℝ) :
    (P.L ⬝ᵥ P.Q *ᵥ P.L) * (x ⬝ᵥ P.Q *ᵥ x) ≤ (P.L ⬝ᵥ P.Q *ᵥ x) ^ 2 := by
  have := (P.hodgeRiemann_iff_weilPSD.mp h) x
  linarith

end LefschetzD2
end T3T5Stage0
end JensenLadder
