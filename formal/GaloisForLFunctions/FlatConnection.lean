import Mathlib

/-!
# Flat multi-q connection algebra

This file formalizes the group-algebra core of
`docs/drafts/multi-q-difference-galois-foundations.md` §16.1 and §16.4:
the pairwise cocycle condition
`A_p * act_p(A_q) = A_q * act_q(A_p)` and its curvature form.

It deliberately does not define Picard-Vessiot rings, Tannakian categories,
matrix bundles, tensor operations, or subquotients. The ledger here is only the
noncommutative algebra needed to state flatness and finite truncation honestly.

One diagnostic theorem records an order issue in the draft text: the written
curvature `A_q⁻¹ * act_q(A_p)⁻¹ * A_p * act_p(A_q)` is not the inverse of
`A_q * act_q(A_p)` in a noncommutative group, so it corresponds to a different
"twisted" order condition.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Pairwise cocycle/integrability condition for connection coefficients. -/
def cocycleCondition {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) : Prop :=
  A p * act p (A q) = A q * act q (A p)

/-- Correct noncommutative discrete curvature:
`(A_q * act_q(A_p))⁻¹ * (A_p * act_p(A_q))`. -/
def discreteCurvature {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) : G :=
  (A q * act q (A p))⁻¹ * (A p * act p (A q))

/-- Vanishing of the corrected discrete curvature is exactly the cocycle condition. -/
theorem discreteCurvature_eq_one_iff_cocycleCondition {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) :
    discreteCurvature act A p q = 1 ↔ cocycleCondition act A p q := by
  unfold discreteCurvature cocycleCondition
  rw [inv_mul_eq_one]
  constructor <;> intro h <;> exact h.symm

/-- The curvature order written in the draft text. This is kept as a diagnostic
object because the order matters for matrix-valued coefficients. -/
def draftOrderCurvature {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) : G :=
  (A q)⁻¹ * (act q (A p))⁻¹ * A p * act p (A q)

/-- The draft-order curvature vanishes exactly for a different, twisted order:
`A_p * act_p(A_q) = act_q(A_p) * A_q`. This exposes the noncommutative order
issue; it is not the stated cocycle condition unless the relevant factors
commute. -/
theorem draftOrderCurvature_eq_one_iff_twisted_cocycle {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (p q : ι) :
    draftOrderCurvature act A p q = 1 ↔
      A p * act p (A q) = act q (A p) * A q := by
  unfold draftOrderCurvature
  constructor
  · intro h
    calc
      A p * act p (A q)
          = act q (A p) *
              (A q * ((A q)⁻¹ * (act q (A p))⁻¹ * A p * act p (A q))) := by
              group
      _ = act q (A p) * (A q * 1) := by rw [h]
      _ = act q (A p) * A q := by group
  · intro h
    calc
      (A q)⁻¹ * (act q (A p))⁻¹ * A p * act p (A q)
          = (A q)⁻¹ * (act q (A p))⁻¹ * (A p * act p (A q)) := by
              group
      _ = (A q)⁻¹ * (act q (A p))⁻¹ * (act q (A p) * A q) := by rw [h]
      _ = 1 := by group

/-- Pairwise integrability restricted to a finite set of operators. -/
def integrableOn {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (S : Finset ι) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, cocycleCondition act A p q

/-- Finite truncation preserves integrability: if a larger finite operator set
is integrable, every smaller finite subset is integrable. -/
theorem integrableOn_mono {ι G : Type*} [Group G]
    {act : ι → G → G} {A : ι → G} {S T : Finset ι}
    (hST : S ⊆ T) :
    integrableOn act A T → integrableOn act A S := by
  intro h p hp q hq
  exact h p (hST hp) q (hST hq)

/-- A globally pairwise-integrable family is integrable on every finite operator
set. -/
theorem integrableOn_of_forall {ι G : Type*} [Group G]
    {act : ι → G → G} {A : ι → G} (S : Finset ι)
    (h : ∀ p q, cocycleCondition act A p q) :
    integrableOn act A S := by
  intro p _ q _
  exact h p q

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Composite image of a fundamental solution under two semilinear difference
operators, using the convention `σᵢ(X)=Aᵢ X`. Applying `σᵢ` after `σⱼ` gives
`σᵢ(Aⱼ) Aᵢ X`. -/
def coextensionComposite {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (i j : ι) (X : G) : G :=
  act i (A j) * A i * X

/-- The flatness condition for commuting co-extended fundamental-solution maps
under the convention `σᵢ(X)=Aᵢ X`. -/
def coextensionFlatCondition {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (i j : ι) : Prop :=
  act i (A j) * A i = act j (A i) * A j

/-- At any invertible fundamental solution value, equality of the two composite
co-extension images is exactly the flatness condition. This is the algebraic
heart of the finite multi-operator PV co-extension criterion; no PV ring is
constructed here. -/
theorem coextensionComposite_eq_iff_flatCondition {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (i j : ι) (X : G) :
    coextensionComposite act A i j X = coextensionComposite act A j i X ↔
      coextensionFlatCondition act A i j := by
  unfold coextensionComposite coextensionFlatCondition
  exact mul_right_cancel_iff

/-- The two co-extended maps commute on every fundamental-solution value iff the
flatness relation `σᵢ(Aⱼ) Aᵢ = σⱼ(Aᵢ) Aⱼ` holds. -/
theorem coextension_commutes_iff_flatCondition {ι G : Type*} [Group G]
    (act : ι → G → G) (A : ι → G) (i j : ι) :
    (∀ X : G, coextensionComposite act A i j X = coextensionComposite act A j i X) ↔
      coextensionFlatCondition act A i j := by
  constructor
  · intro h
    exact (coextensionComposite_eq_iff_flatCondition act A i j 1).mp (h 1)
  · intro h X
    exact (coextensionComposite_eq_iff_flatCondition act A i j X).mpr h

end

end GaloisForLFunctions
