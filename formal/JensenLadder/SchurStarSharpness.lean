import JensenLadder.SchurStarDominationCarrier

/-!
# Sharpness of the Schur-star domination budget

`SchurStarDominationCarrier` proves that a central diagonal `arch` controls the
whole star row if the quadratic response budget is at most `arch`.

This module records the converse route-control fact, under the natural
nondegeneracy condition that every leaf square-root diagonal is nonzero: if
`arch < responseBudget`, then the completed star form has a negative vector.
Thus the Schur-star row cannot be discharged by a weaker budget inequality.

This is a finite sharpness/falsifier artifact only.  It does not prove the zeta
response budget, construct the global carrier, or prove RH.  Theorem M is
proven, but Theorem M does not prove RH by itself.

Evidence class: formal/certificate artifact and dead-end elimination.
-/

namespace JensenLadder
namespace SchurStarDominationCarrier

namespace StarAssembly

variable {Edge : Type*} [Fintype Edge]

/-- All completed Schur-star forms associated to this assembly are nonnegative. -/
def AllFormsNonnegative (A : StarAssembly Edge) : Prop :=
  forall x : ℝ, forall y : Edge -> ℝ, 0 <= A.form x y

/-- The response budget is a sum of squares. -/
theorem responseBudget_nonnegative (A : StarAssembly Edge) :
    0 <= A.responseBudget := by
  unfold responseBudget
  exact Finset.sum_nonneg (fun e _he => sq_nonneg (A.response e))

/--
The non-strict Schur-star domination theorem.

The original carrier theorem assumes `0 < arch`.  The only missing endpoint is
`arch = responseBudget = 0`; there Cauchy--Schwarz forces the coupling sum to
vanish, so the form reduces to the nonnegative leaf energy.
-/
theorem allFormsNonnegative_of_responseBudget_le_arch
    (A : StarAssembly Edge)
    (hbudget : A.responseBudget <= A.arch) :
    A.AllFormsNonnegative := by
  intro x y
  have harch_nonneg : 0 <= A.arch :=
    le_trans A.responseBudget_nonnegative hbudget
  by_cases harch_zero : A.arch = 0
  · have hresponse_le_zero : A.responseBudget <= 0 := by
      simpa [harch_zero] using hbudget
    have hresponse_zero : A.responseBudget = 0 :=
      le_antisymm hresponse_le_zero A.responseBudget_nonnegative
    have hcouple_sq_le_zero : A.couplingSum y ^ 2 <= 0 := by
      have hcouple := A.couplingSum_sq_le_responseBudget_mul_leafEnergy y
      simpa [hresponse_zero] using hcouple
    have hcouple_zero : A.couplingSum y = 0 := by
      have hcouple_sq_zero : A.couplingSum y ^ 2 = 0 :=
        le_antisymm hcouple_sq_le_zero (sq_nonneg (A.couplingSum y))
      exact sq_eq_zero_iff.mp hcouple_sq_zero
    simpa [form, harch_zero, hcouple_zero] using A.leafEnergy_nonnegative y
  · have harch_pos : 0 < A.arch := by
      exact lt_of_le_of_ne harch_nonneg (Ne.symm harch_zero)
    exact A.form_nonnegative_of_responseBudget_le_arch x y harch_pos hbudget

/--
If every leaf square-root diagonal is nonzero, and the response budget exceeds
the central diagonal, then the Schur-star form has a negative vector.

The witness chooses `leafValue y e = response e` and `x = -1`, reducing the form
to `arch - responseBudget`.
-/
theorem exists_negative_form_of_arch_lt_responseBudget
    (A : StarAssembly Edge)
    (hroot : forall e : Edge, A.root e ≠ 0)
    (hbad : A.arch < A.responseBudget) :
    exists x : ℝ, exists y : Edge -> ℝ, A.form x y < 0 := by
  let y : Edge -> ℝ := fun e => A.response e / A.root e
  have hleaf : forall e : Edge, A.leafValue y e = A.response e := by
    intro e
    unfold leafValue y
    field_simp [hroot e]
  have hcouple : A.couplingSum y = A.responseBudget := by
    unfold couplingSum responseBudget
    apply Finset.sum_congr rfl
    intro e _he
    rw [hleaf e]
    ring
  have henergy : A.leafEnergy y = A.responseBudget := by
    unfold leafEnergy responseBudget
    apply Finset.sum_congr rfl
    intro e _he
    rw [hleaf e]
  refine ⟨-1, y, ?_⟩
  unfold form
  rw [hcouple, henergy]
  nlinarith

/-- A strict response-budget overshoot refutes nonnegativity of all star forms. -/
theorem not_allFormsNonnegative_of_arch_lt_responseBudget
    (A : StarAssembly Edge)
    (hroot : forall e : Edge, A.root e ≠ 0)
    (hbad : A.arch < A.responseBudget) :
    Not A.AllFormsNonnegative := by
  intro hnonneg
  rcases A.exists_negative_form_of_arch_lt_responseBudget hroot hbad with
    ⟨x, y, hneg⟩
  exact (not_le_of_gt hneg) (hnonneg x y)

/--
With nonzero leaf roots, the Schur-star response-budget inequality is exactly
equivalent to nonnegativity of all completed star forms.
-/
theorem allFormsNonnegative_iff_responseBudget_le_arch
    (A : StarAssembly Edge)
    (hroot : forall e : Edge, A.root e ≠ 0) :
    A.AllFormsNonnegative ↔ A.responseBudget <= A.arch := by
  constructor
  · intro hnonneg
    by_contra hbudget
    exact A.not_allFormsNonnegative_of_arch_lt_responseBudget hroot
      (lt_of_not_ge hbudget) hnonneg
  · exact A.allFormsNonnegative_of_responseBudget_le_arch

end StarAssembly

/-- Packaged sufficient Schur-star domination certificate. -/
structure SchurStarCertificate (Edge : Type*) [Fintype Edge] where
  assembly : StarAssembly Edge
  archPositive : 0 < assembly.arch
  responseBudget_le_arch : assembly.responseBudget <= assembly.arch

namespace SchurStarCertificate

variable {Edge : Type*} [Fintype Edge]

/-- The packaged certificate proves nonnegativity of every completed star form. -/
theorem allFormsNonnegative
    (C : SchurStarCertificate Edge) :
    C.assembly.AllFormsNonnegative := by
  intro x y
  exact C.assembly.form_nonnegative_of_responseBudget_le_arch
    x y C.archPositive C.responseBudget_le_arch

end SchurStarCertificate

/-- Packaged strict-budget falsifier for the Schur-star domination row. -/
structure SchurStarFalsifier (Edge : Type*) [Fintype Edge] where
  assembly : StarAssembly Edge
  rootsNonzero : forall e : Edge, assembly.root e ≠ 0
  arch_lt_responseBudget : assembly.arch < assembly.responseBudget

namespace SchurStarFalsifier

variable {Edge : Type*} [Fintype Edge]

/-- The packaged falsifier supplies an explicit negative star-form vector. -/
theorem exists_negative_form
    (F : SchurStarFalsifier Edge) :
    exists x : ℝ, exists y : Edge -> ℝ, F.assembly.form x y < 0 :=
  F.assembly.exists_negative_form_of_arch_lt_responseBudget
    F.rootsNonzero F.arch_lt_responseBudget

/-- The packaged falsifier rules out global nonnegativity of the star form. -/
theorem not_allFormsNonnegative
    (F : SchurStarFalsifier Edge) :
    Not F.assembly.AllFormsNonnegative :=
  F.assembly.not_allFormsNonnegative_of_arch_lt_responseBudget
    F.rootsNonzero F.arch_lt_responseBudget

end SchurStarFalsifier

end SchurStarDominationCarrier
end JensenLadder
