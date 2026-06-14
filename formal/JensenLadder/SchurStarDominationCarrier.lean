import Mathlib.Tactic

/-!
# Schur star domination carrier

This module records a finite Schur-complement / Cauchy-Schwarz domination
certificate.

The star has one central coordinate `x` with diagonal `arch`, and finitely many
leaf coordinates `y e`.  Each leaf has square-root diagonal `root e`, and the
central-leaf coupling factors as

```text
  coupling e = response e * root e.
```

If the central diagonal dominates the quadratic response budget

```text
  sum_e response(e)^2 <= arch,
```

then the signed star form

```text
  arch*x^2 + 2*x*sum_e response(e)*root(e)*y(e)
    + sum_e (root(e)*y(e))^2
```

is nonnegative.  This is a finite nonlocal row-domination baby carrier: a
single global diagonal controls a whole row through an `l2` budget, not by
edgewise absolute domination.

This does not identify the zeta Weil form with such a star block and does not
prove RH.  A zeta application would still need an Euler-loaded/arithmetic
reason for the response-budget inequality.  Theorem M is proven, but Theorem M
does not prove RH by itself.

Evidence class: formal/certificate artifact; proved lemma.
-/

namespace JensenLadder
namespace SchurStarDominationCarrier

/-- A finite star block with one central diagonal and square-root leaf diagonals. -/
structure StarAssembly (Edge : Type*) where
  arch : ℝ
  root : Edge -> ℝ
  response : Edge -> ℝ

namespace StarAssembly

variable {Edge : Type*} [Fintype Edge]

/-- The leaf value after applying the square-root diagonal. -/
def leafValue (A : StarAssembly Edge) (y : Edge -> ℝ) (e : Edge) : ℝ :=
  A.root e * y e

/-- The leaf diagonal energy. -/
def leafEnergy (A : StarAssembly Edge) (y : Edge -> ℝ) : ℝ :=
  ∑ e : Edge, A.leafValue y e ^ 2

/-- The quadratic response budget of the central row. -/
def responseBudget (A : StarAssembly Edge) : ℝ :=
  ∑ e : Edge, A.response e ^ 2

/-- The central-leaf coupling sum. -/
def couplingSum (A : StarAssembly Edge) (y : Edge -> ℝ) : ℝ :=
  ∑ e : Edge, A.response e * A.leafValue y e

/-- The completed Schur-star quadratic form. -/
def form (A : StarAssembly Edge) (x : ℝ) (y : Edge -> ℝ) : ℝ :=
  A.arch * x ^ 2 + 2 * x * A.couplingSum y + A.leafEnergy y

/-- The leaf energy is nonnegative. -/
theorem leafEnergy_nonnegative (A : StarAssembly Edge) (y : Edge -> ℝ) :
    0 <= A.leafEnergy y := by
  unfold leafEnergy
  exact Finset.sum_nonneg (fun e _ => sq_nonneg (A.leafValue y e))

/-- Cauchy-Schwarz controls the square of the coupling sum. -/
theorem couplingSum_sq_le_responseBudget_mul_leafEnergy
    (A : StarAssembly Edge) (y : Edge -> ℝ) :
    A.couplingSum y ^ 2 <= A.responseBudget * A.leafEnergy y := by
  simpa [couplingSum, responseBudget, leafEnergy] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Edge)
      (fun e : Edge => A.response e)
      (fun e : Edge => A.leafValue y e))

/-- If the central diagonal dominates the response budget, it controls the row. -/
theorem couplingSum_sq_le_arch_mul_leafEnergy
    (A : StarAssembly Edge) (y : Edge -> ℝ)
    (hbudget : A.responseBudget <= A.arch) :
    A.couplingSum y ^ 2 <= A.arch * A.leafEnergy y := by
  exact le_trans (A.couplingSum_sq_le_responseBudget_mul_leafEnergy y)
    (mul_le_mul_of_nonneg_right hbudget (A.leafEnergy_nonnegative y))

/--
The Schur-star domination certificate.

If `arch > 0` and the response budget is at most `arch`, then the completed
star form is nonnegative for every central coordinate and leaf vector.
-/
theorem form_nonnegative_of_responseBudget_le_arch
    (A : StarAssembly Edge) (x : ℝ) (y : Edge -> ℝ)
    (harch : 0 < A.arch)
    (hbudget : A.responseBudget <= A.arch) :
    0 <= A.form x y := by
  have hcouple : A.couplingSum y ^ 2 <= A.arch * A.leafEnergy y :=
    A.couplingSum_sq_le_arch_mul_leafEnergy y hbudget
  have hsq : 0 <= (A.arch * x + A.couplingSum y) ^ 2 := sq_nonneg _
  have hmul : 0 <= A.arch * A.form x y := by
    unfold form
    nlinarith
  have hmul2 : 0 <= A.form x y * A.arch := by
    nlinarith
  exact nonneg_of_mul_nonneg_left hmul2 harch

end StarAssembly

end SchurStarDominationCarrier
end JensenLadder

namespace JensenLadder
namespace SchurStarDominationCarrier
namespace StarAssembly

/-!
## Sharpness of the Schur-star response budget

If every leaf root is nonzero, the response-budget condition is also necessary:
choosing `y e = -response e / root e` realizes the negative Schur-complement
witness whenever the central diagonal is too small.
-/

variable {Edge : Type*} [Fintype Edge]

/-- The test vector that saturates the Schur-complement budget. -/
noncomputable def sharpnessWitness (A : StarAssembly Edge) : Edge -> ℝ :=
  fun e => - A.response e / A.root e

omit [Fintype Edge] in
/-- With nonzero roots, the sharpness witness has leaf value `-response e`. -/
theorem leafValue_sharpnessWitness
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0)
    (e : Edge) :
    A.leafValue A.sharpnessWitness e = - A.response e := by
  unfold leafValue sharpnessWitness
  field_simp [hroot e]

/-- The sharpness witness has leaf energy equal to the response budget. -/
theorem leafEnergy_sharpnessWitness
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0) :
    A.leafEnergy A.sharpnessWitness = A.responseBudget := by
  unfold leafEnergy responseBudget
  apply Finset.sum_congr rfl
  intro e _
  rw [leafValue_sharpnessWitness A hroot e]
  ring

/-- The sharpness witness makes the coupling sum equal to `-responseBudget`. -/
theorem couplingSum_sharpnessWitness
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0) :
    A.couplingSum A.sharpnessWitness = - A.responseBudget := by
  unfold couplingSum responseBudget
  calc
    (∑ e : Edge, A.response e * A.leafValue A.sharpnessWitness e)
        = ∑ e : Edge, -(A.response e ^ 2) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [leafValue_sharpnessWitness A hroot e]
          ring
    _ = - ∑ e : Edge, A.response e ^ 2 := by
          rw [Finset.sum_neg_distrib]

/-- At the sharpness witness, the form is exactly `arch - responseBudget`. -/
theorem form_one_sharpnessWitness
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0) :
    A.form 1 A.sharpnessWitness = A.arch - A.responseBudget := by
  unfold form
  rw [couplingSum_sharpnessWitness A hroot, leafEnergy_sharpnessWitness A hroot]
  ring

/-- If the Schur-star form is nonnegative for all inputs, the response budget is necessary. -/
theorem responseBudget_le_arch_of_form_nonnegative
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0)
    (hnonneg : ∀ x : ℝ, ∀ y : Edge -> ℝ, 0 <= A.form x y) :
    A.responseBudget <= A.arch := by
  have h := hnonneg 1 A.sharpnessWitness
  rw [form_one_sharpnessWitness A hroot] at h
  linarith

/-- If the central diagonal is below the response budget, an explicit negative vector exists. -/
theorem exists_negative_of_arch_lt_responseBudget
    (A : StarAssembly Edge)
    (hroot : ∀ e : Edge, A.root e ≠ 0)
    (h : A.arch < A.responseBudget) :
    ∃ x : ℝ, ∃ y : Edge -> ℝ, A.form x y < 0 := by
  refine ⟨1, A.sharpnessWitness, ?_⟩
  rw [form_one_sharpnessWitness A hroot]
  linarith

/-- With positive central diagonal and nonzero roots, the Schur-star budget condition is exact. -/
theorem form_nonnegative_iff_responseBudget_le_arch
    (A : StarAssembly Edge)
    (harch : 0 < A.arch)
    (hroot : ∀ e : Edge, A.root e ≠ 0) :
    (∀ x : ℝ, ∀ y : Edge -> ℝ, 0 <= A.form x y) ↔ A.responseBudget <= A.arch := by
  constructor
  · exact responseBudget_le_arch_of_form_nonnegative A hroot
  · intro hbudget x y
    exact A.form_nonnegative_of_responseBudget_le_arch x y harch hbudget

end StarAssembly
end SchurStarDominationCarrier
end JensenLadder

namespace JensenLadder
namespace SchurStarDominationCarrier
namespace StarAssembly

/-!
## Square/projection identity for the Schur-star carrier

Multiplying the star form by the positive central diagonal exposes it as one
square plus the Cauchy-Schwarz residual.
-/

variable {Edge : Type*} [Fintype Edge]

/-- The Cauchy-Schwarz residual in the Schur-star square/projection identity. -/
def projectionResidual (A : StarAssembly Edge) (y : Edge -> ℝ) : ℝ :=
  A.arch * A.leafEnergy y - A.couplingSum y ^ 2

/-- The exact square/projection identity behind Schur-star positivity. -/
theorem arch_mul_form_eq_square_add_projectionResidual
    (A : StarAssembly Edge) (x : ℝ) (y : Edge -> ℝ) :
    A.arch * A.form x y
      = (A.arch * x + A.couplingSum y) ^ 2 + A.projectionResidual y := by
  unfold form projectionResidual
  ring

/-- The projection residual is nonnegative when the response budget is dominated by `arch`. -/
theorem projectionResidual_nonnegative_of_responseBudget_le_arch
    (A : StarAssembly Edge) (y : Edge -> ℝ)
    (hbudget : A.responseBudget <= A.arch) :
    0 <= A.projectionResidual y := by
  have hcouple : A.couplingSum y ^ 2 <= A.arch * A.leafEnergy y :=
    A.couplingSum_sq_le_arch_mul_leafEnergy y hbudget
  unfold projectionResidual
  linarith

/-- The square/projection identity gives nonnegativity after multiplying by `arch`. -/
theorem arch_mul_form_nonnegative_of_responseBudget_le_arch
    (A : StarAssembly Edge) (x : ℝ) (y : Edge -> ℝ)
    (hbudget : A.responseBudget <= A.arch) :
    0 <= A.arch * A.form x y := by
  rw [arch_mul_form_eq_square_add_projectionResidual]
  exact add_nonneg (sq_nonneg _) (A.projectionResidual_nonnegative_of_responseBudget_le_arch y hbudget)

/-- The named square/projection proof of Schur-star nonnegativity. -/
theorem form_nonnegative_from_projection_identity
    (A : StarAssembly Edge) (x : ℝ) (y : Edge -> ℝ)
    (harch : 0 < A.arch)
    (hbudget : A.responseBudget <= A.arch) :
    0 <= A.form x y := by
  have hmul : 0 <= A.arch * A.form x y :=
    A.arch_mul_form_nonnegative_of_responseBudget_le_arch x y hbudget
  have hmul2 : 0 <= A.form x y * A.arch := by
    nlinarith
  exact nonneg_of_mul_nonneg_left hmul2 harch

end StarAssembly
end SchurStarDominationCarrier
end JensenLadder
