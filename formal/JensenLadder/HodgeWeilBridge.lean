import JensenLadder.CCMFiniteWeil

/-!
# Finite Hodge-to-Weil positivity bridge

This module formalizes the elementary algebra consumed by the F1/Hodge route at
a finite semilocal truncation.

If a finite CCM/Sonin/semilocal Weil matrix is realized as the negative
self-intersection of primitive divisor classes, and the Hodge-index row says
primitive self-intersections are nonpositive, then the finite Weil quadratic form
is positive semidefinite.

This file does not construct the arithmetic surface, divisor classes,
intersection theory, trace identity, semilocal Connes operator, convergence
theorem, or RH.  It only records the finite algebraic bridge that such a
construction must instantiate.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace HodgeWeilBridge

open scoped BigOperators
open CCMFiniteWeil

universe u

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/--
The finite quadratic form associated to a semilocal Weil matrix.

No symmetry is assumed here.  Symmetry/self-adjointness is a separate matrix row
already represented in `CCMFiniteWeil.entry_swap_eq_of_symmetric`.
-/
noncomputable def quadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, v i * entry D i j * v j

/-- Archimedean part of the finite semilocal Weil quadratic form. -/
noncomputable def archQuadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, v i * archPart D i j * v j

/-- Prime/local perturbation part of the finite semilocal Weil quadratic form. -/
noncomputable def primeQuadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, v i * primePart D i j * v j

/-- One local row's contribution to the prime/local quadratic form. -/
noncomputable def localPrimeQuadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (q : κ) (v : ι -> ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    v i * (D.primeCoeff q * D.primeKernel q i j) * v j

/-- The finite semilocal Weil quadratic form is the archimedean part minus the
prime/local perturbation part. -/
theorem quadraticForm_eq_arch_sub_prime
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) :
    quadraticForm D v = archQuadraticForm D v - primeQuadraticForm D v := by
  calc
    quadraticForm D v =
        ∑ i : ι, ∑ j : ι,
          (v i * archPart D i j * v j -
            v i * primePart D i j * v j) := by
      unfold quadraticForm
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [entry]
      ring
    _ = ∑ i : ι,
          ((∑ j : ι, v i * archPart D i j * v j) -
            (∑ j : ι, v i * primePart D i j * v j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact
        (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset ι))
          (f := fun j : ι => v i * archPart D i j * v j)
          (g := fun j : ι => v i * primePart D i j * v j))
    _ = archQuadraticForm D v - primeQuadraticForm D v := by
      rw [archQuadraticForm, primeQuadraticForm]
      exact
        (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset ι))
          (f := fun i : ι => ∑ j : ι, v i * archPart D i j * v j)
          (g := fun i : ι => ∑ j : ι, v i * primePart D i j * v j))

/-- The prime/local quadratic form is the finite sum of its local-row
contributions. -/
theorem primeQuadraticForm_eq_sum_localPrimeQuadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) :
    primeQuadraticForm D v =
      ∑ q : κ, localPrimeQuadraticForm D q v := by
  let f : ι -> ι -> κ -> ℝ :=
    fun i j q => v i * (D.primeCoeff q * D.primeKernel q i j) * v j
  calc
    primeQuadraticForm D v = ∑ i : ι, ∑ j : ι, ∑ q : κ, f i j q := by
      unfold primeQuadraticForm
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      simp [primePart, f, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : ι, ∑ q : κ, ∑ j : ι, f i j q := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Finset.sum_comm
    _ = ∑ q : κ, ∑ i : ι, ∑ j : ι, f i j q := by
      exact Finset.sum_comm
    _ = ∑ q : κ, localPrimeQuadraticForm D q v := by
      simp [localPrimeQuadraticForm, f]

/-- Fully expanded semilocal split: archimedean quadratic form minus the sum of
local prime-row quadratic forms. -/
theorem quadraticForm_eq_arch_sub_sum_localPrimeQuadraticForm
    (D : SemilocalFiniteWeilData ι κ ℝ) (v : ι -> ℝ) :
    quadraticForm D v =
      archQuadraticForm D v -
        ∑ q : κ, localPrimeQuadraticForm D q v := by
  rw [quadraticForm_eq_arch_sub_prime,
    primeQuadraticForm_eq_sum_localPrimeQuadraticForm]

/-- Positive semidefiniteness of the finite semilocal Weil quadratic form. -/
def PositiveSemidefinite
    (D : SemilocalFiniteWeilData ι κ ℝ) : Prop :=
  ∀ v : ι -> ℝ, 0 ≤ quadraticForm D v

/-- A finite vector witnessing a negative direction of the semilocal Weil form. -/
def HasNegativeVector
    (D : SemilocalFiniteWeilData ι κ ℝ) : Prop :=
  ∃ v : ι -> ℝ, quadraticForm D v < 0

/-- A negative vector falsifies positive semidefiniteness. -/
theorem not_positiveSemidefinite_of_negative_quadraticForm
    {D : SemilocalFiniteWeilData ι κ ℝ} {v : ι -> ℝ}
    (hv : quadraticForm D v < 0) :
    ¬ PositiveSemidefinite D := by
  intro hpsd
  exact (not_le_of_gt hv) (hpsd v)

/-- Any negative vector falsifies positive semidefiniteness. -/
theorem not_positiveSemidefinite_of_hasNegativeVector
    {D : SemilocalFiniteWeilData ι κ ℝ}
    (hneg : HasNegativeVector D) :
    ¬ PositiveSemidefinite D := by
  rcases hneg with ⟨v, hv⟩
  exact not_positiveSemidefinite_of_negative_quadraticForm hv

/--
A finite Hodge realization of a semilocal Weil matrix.

`DivisorClass`, `intersectionForm`, and `primitive` are intentionally abstract.
The load-bearing rows are:

* every finite vector maps to a primitive divisor class;
* primitive self-intersections are nonpositive;
* the finite Weil quadratic form is exactly the negative self-intersection of
  the realized divisor class.

Supplying those rows for a concrete semilocal truncation is the arithmetic
geometry/operator work; this structure only consumes them.
-/
structure FiniteHodgeRealization
    (D : SemilocalFiniteWeilData ι κ ℝ) where
  DivisorClass : Type u
  intersectionForm : DivisorClass -> DivisorClass -> ℝ
  primitive : DivisorClass -> Prop
  realize : (ι -> ℝ) -> DivisorClass
  primitive_realize : ∀ v : ι -> ℝ, primitive (realize v)
  hodgeIndex_nonpos :
    ∀ X : DivisorClass, primitive X -> intersectionForm X X ≤ 0
  quadratic_eq_neg_intersection :
    ∀ v : ι -> ℝ,
      quadraticForm D v = - intersectionForm (realize v) (realize v)

namespace FiniteHodgeRealization

variable {D : SemilocalFiniteWeilData ι κ ℝ}

/-- The realized divisor class of every finite vector has nonpositive
self-intersection. -/
theorem selfIntersection_nonpos
    (H : FiniteHodgeRealization.{u} D)
    (v : ι -> ℝ) :
    H.intersectionForm (H.realize v) (H.realize v) ≤ 0 :=
  H.hodgeIndex_nonpos (H.realize v) (H.primitive_realize v)

/-- The finite semilocal Weil quadratic form is nonnegative under a Hodge
realization. -/
theorem quadraticForm_nonnegative
    (H : FiniteHodgeRealization.{u} D)
    (v : ι -> ℝ) :
    0 ≤ quadraticForm D v := by
  rw [H.quadratic_eq_neg_intersection v]
  linarith [selfIntersection_nonpos H v]

/-- A finite Hodge realization supplies positive semidefiniteness of the
semilocal Weil matrix. -/
theorem positiveSemidefinite
    (H : FiniteHodgeRealization.{u} D) :
    PositiveSemidefinite D := by
  intro v
  exact quadraticForm_nonnegative H v

/-- A negative quadratic-form value rules out this finite Hodge realization. -/
theorem false_of_negative_quadraticForm
    (H : FiniteHodgeRealization.{u} D)
    {v : ι -> ℝ}
    (hv : quadraticForm D v < 0) :
    False :=
  not_positiveSemidefinite_of_negative_quadraticForm hv H.positiveSemidefinite

end FiniteHodgeRealization

/-- A negative vector rules out the existence of any finite Hodge realization for
the semilocal matrix. -/
theorem not_nonempty_hodgeRealization_of_negative_quadraticForm
    {D : SemilocalFiniteWeilData ι κ ℝ} {v : ι -> ℝ}
    (hv : quadraticForm D v < 0) :
    ¬ Nonempty (FiniteHodgeRealization.{u} D) := by
  rintro ⟨H⟩
  exact H.false_of_negative_quadraticForm hv

/-- Any negative vector rules out the existence of a finite Hodge realization for
the semilocal matrix. -/
theorem not_nonempty_hodgeRealization_of_hasNegativeVector
    {D : SemilocalFiniteWeilData ι κ ℝ}
    (hneg : HasNegativeVector D) :
    ¬ Nonempty (FiniteHodgeRealization.{u} D) := by
  rcases hneg with ⟨v, hv⟩
  exact not_nonempty_hodgeRealization_of_negative_quadraticForm hv

/-- Packaged certificate for finite semilocal Weil positivity via Hodge index. -/
structure FiniteHodgeWeilCertificate where
  data : SemilocalFiniteWeilData ι κ ℝ
  hodgeRealization : FiniteHodgeRealization.{u} data

namespace FiniteHodgeWeilCertificate

/-- The packaged certificate supplies positive semidefiniteness of its finite
semilocal Weil form. -/
theorem positiveSemidefinite
    (C : FiniteHodgeWeilCertificate.{u} (ι := ι) (κ := κ)) :
    PositiveSemidefinite C.data :=
  C.hodgeRealization.positiveSemidefinite

/-- Pointwise nonnegativity of the packaged finite semilocal Weil quadratic form. -/
theorem quadraticForm_nonnegative
    (C : FiniteHodgeWeilCertificate.{u} (ι := ι) (κ := κ))
    (v : ι -> ℝ) :
    0 ≤ quadraticForm C.data v :=
  C.hodgeRealization.quadraticForm_nonnegative v

end FiniteHodgeWeilCertificate

/-- Packaged finite negative-direction falsifier for a semilocal Weil matrix. -/
structure FiniteHodgeWeilFalsifier where
  data : SemilocalFiniteWeilData ι κ ℝ
  vector : ι -> ℝ
  quadraticForm_lt_zero : quadraticForm data vector < 0

namespace FiniteHodgeWeilFalsifier

/-- The packaged negative vector is a negative-vector witness. -/
theorem hasNegativeVector
    (F : FiniteHodgeWeilFalsifier (ι := ι) (κ := κ)) :
    HasNegativeVector F.data :=
  ⟨F.vector, F.quadraticForm_lt_zero⟩

/-- A packaged finite negative vector falsifies positive semidefiniteness. -/
theorem not_positiveSemidefinite
    (F : FiniteHodgeWeilFalsifier (ι := ι) (κ := κ)) :
    ¬ PositiveSemidefinite F.data :=
  not_positiveSemidefinite_of_negative_quadraticForm F.quadraticForm_lt_zero

/-- A packaged finite negative vector rules out any finite Hodge realization of
the same semilocal matrix. -/
theorem not_nonempty_hodgeRealization
    (F : FiniteHodgeWeilFalsifier (ι := ι) (κ := κ)) :
    ¬ Nonempty (FiniteHodgeRealization.{u} F.data) :=
  not_nonempty_hodgeRealization_of_negative_quadraticForm
    F.quadraticForm_lt_zero

end FiniteHodgeWeilFalsifier

end HodgeWeilBridge
end JensenLadder
