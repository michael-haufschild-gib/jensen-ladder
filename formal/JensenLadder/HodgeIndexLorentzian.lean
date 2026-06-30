import Mathlib

/-!
# Abstract Hodge-index ⟺ Lorentzian reverse-Cauchy–Schwarz (d = 2)

This module supplies the concrete linear-algebra core that `HodgeIndexCarrier`
deliberately leaves abstract ("it only names the rows").  It is the algebraic
heart of **Stage 0 / Stage 2** of the T3/T5 self-product construction program
(`docs/plans/program_T3_T5_self_product_construction_20260617.md`; worklog
`docs/rh/dyson_stage2_lorentzian_secular_20260617.md`).

For a degree-2 Hodge structure the degree-1 piece `A₁` carries a symmetric
intersection form `Q` and an ample/Lefschetz element `L` with `Q(L,L) > 0`.  The
**Hodge–Riemann / Hodge-index** property is that `Q` is negative-semidefinite on
the primitive part `L^⊥ = {x : Q(L,x) = 0}`.  We prove this is *equivalent* to
the **Lorentzian reverse-Cauchy–Schwarz** inequality
`Q(L,x)² ≥ Q(L,L)·Q(x,x)  for all x`,
i.e. positive-semidefiniteness of the rank-one-minus-scaled form
`(QL)(QL)ᵀ − Q(L,L)·Q`.

This is a field-free, finite-dimensional theorem (no arithmetic input).  It makes
precise the reduction "boundary-HR on the codim-1 primitive part ⟺ Weil
positivity ⟺ RH": the first `⟺` is `hodge_index_iff` below; the second is Weil's
criterion, applied in the limit, and is **not** proved here.

**Honesty caveat (faithful vs measured; cf. `rh_faithful_vs_measured_dichotomy`
and `docs/rh/xi_outer_dilation_worklog_20260617.md` §W6).**  A *finite-dimensional*
HR/PSD statement is the **measured** (type-II₁, density / dust-blind) face of
positivity: it can hold while a sparse off-line zero family escapes.  The
**faithful** off-line functional (every off-line zero counts) is the Littlewood/
Jensen–Nevanlinna defect `Δ_½ = Σ_{off-line}(Re ρ − ½) + singular`, which strictly
dominates the measured index `κ₋`.  So this theorem is the exact finite algebra of
HR positivity; the RH-content lives only in the infinite limit, where measured
positivity must be upgraded to the faithful defect.  Nothing here proves RH.

**Relation to `HodgeIndexInequality`.**  That module proves the *forward*
direction (`hodge_index_ineq`: HR on the polar-complement ⟹ reverse-CS)
abstractly over a real vector space.  This module adds (a) the *converse*
direction, giving the full **iff** (`hodge_index_iff`), and (b) the
**matrix-concrete** form `Q : Matrix ι ι ℝ`, `Q(a,b) = a ⬝ᵥ Q *ᵥ b`, which is the
shape the certified CCM/Weil form `QW` and the secular reconstruction
(`SecularReconstruction`) actually live in — so the criterion is directly
applicable to those objects.

Evidence class: pure linear algebra over `ℝ` (reverse Cauchy–Schwarz via the
shifted-quadratic / vertex argument).  Axiom-clean.
-/

namespace JensenLadder
namespace HodgeIndexLorentzian

open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- Symmetry of the bilinear form `(a, b) ↦ a ⬝ᵥ Q *ᵥ b` for a symmetric matrix
`Q` (`Qᵀ = Q`). -/
theorem bil_symm (Q : Matrix ι ι ℝ) (hQ : Qᵀ = Q) (a b : ι → ℝ) :
    a ⬝ᵥ Q *ᵥ b = b ⬝ᵥ Q *ᵥ a := by
  have hvm : a ᵥ* Q = Q *ᵥ a := by
    rw [← Matrix.vecMul_transpose, hQ]
  rw [Matrix.dotProduct_mulVec, hvm, dotProduct_comm]

/-- **Abstract Hodge-index equivalence (d = 2).**
For a symmetric real matrix `Q` and a vector `L` with `Q(L,L) = L ⬝ᵥ Q *ᵥ L > 0`,
the Hodge–Riemann property (`Q` negative-semidefinite on the `Q`-orthogonal
complement `L^⊥`) is equivalent to the Lorentzian reverse-Cauchy–Schwarz
inequality `Q(L,x)² ≥ Q(L,L)·Q(x,x)` for all `x`.

This is the precise sense in which "the intersection form is (boundary-)Lorentzian
with timelike axis `L`" — exactly one positive direction, the rest `≤ 0`. -/
theorem hodge_index_iff (Q : Matrix ι ι ℝ) (hQ : Qᵀ = Q) (L : ι → ℝ)
    (hL : 0 < L ⬝ᵥ Q *ᵥ L) :
    (∀ x : ι → ℝ, L ⬝ᵥ Q *ᵥ x = 0 → x ⬝ᵥ Q *ᵥ x ≤ 0)
      ↔ (∀ x : ι → ℝ, 0 ≤ (L ⬝ᵥ Q *ᵥ x) ^ 2 - (L ⬝ᵥ Q *ᵥ L) * (x ⬝ᵥ Q *ᵥ x)) := by
  set qLL := L ⬝ᵥ Q *ᵥ L with hqLL
  have hqne : qLL ≠ 0 := ne_of_gt hL
  constructor
  · -- HR ⟹ reverse-Cauchy–Schwarz
    intro hHR x
    set p := L ⬝ᵥ Q *ᵥ x with hp
    set X := x ⬝ᵥ Q *ᵥ x with hX
    set c := p / qLL with hc
    have hexp : (x + (-c) • L) ⬝ᵥ Q *ᵥ (x + (-c) • L)
        = X - 2 * c * p + c ^ 2 * qLL := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
        dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [bil_symm Q hQ x L]
      ring
    have hLy : L ⬝ᵥ Q *ᵥ (x + (-c) • L) = 0 := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        smul_eq_mul]
      rw [← hp, ← hqLL, hc]; field_simp; ring
    have hyy : (x + (-c) • L) ⬝ᵥ Q *ᵥ (x + (-c) • L) ≤ 0 := hHR _ hLy
    rw [hexp] at hyy
    have hc2 : c * qLL = p := by rw [hc]; field_simp
    nlinarith [hyy, hL, mul_pos hL hL, sq_nonneg c, hc2]
  · -- reverse-Cauchy–Schwarz ⟹ HR
    intro hCS x hx
    have h := hCS x
    rw [hx] at h
    nlinarith [h, hL]

/-- The right-hand side of `hodge_index_iff` is exactly the quadratic form of the
matrix `(Q *ᵥ L) (Q *ᵥ L)ᵀ − (L ⬝ᵥ Q *ᵥ L) • Q` evaluated at `x`
(`= (L⬝ᵥQ*ᵥx)² − (L⬝ᵥQ*ᵥL)(x⬝ᵥQ*ᵥx)`); positivity of this form for all `x` is the
Lorentzian/PSD statement.  We keep the criterion in pointwise quadratic-form shape
(above), which is the directly usable form and avoids the `MulOpposite` scalar in
`Matrix.vecMulVec_mulVec`. -/
theorem hodge_index_reverseCS (Q : Matrix ι ι ℝ) (hQ : Qᵀ = Q) (L : ι → ℝ)
    (hL : 0 < L ⬝ᵥ Q *ᵥ L)
    (hHR : ∀ x : ι → ℝ, L ⬝ᵥ Q *ᵥ x = 0 → x ⬝ᵥ Q *ᵥ x ≤ 0) (x : ι → ℝ) :
    (L ⬝ᵥ Q *ᵥ L) * (x ⬝ᵥ Q *ᵥ x) ≤ (L ⬝ᵥ Q *ᵥ x) ^ 2 := by
  have := (hodge_index_iff Q hQ L hL).mp hHR x
  linarith

end HodgeIndexLorentzian
end JensenLadder
