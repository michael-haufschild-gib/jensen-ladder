import Mathlib

/-!
# Rank-one scalar difference cohomology

`multi-q-difference-galois-foundations.md` §17.1 identifies rank-one multi-`q`
modules with scalar cocycles

`a_p * σ_p(a_q) = a_q * σ_q(a_p)`

modulo scalar coboundaries `σ_p(h) / h`. This file formalizes the finite group-algebra
skeleton behind that statement for an arbitrary commutative coefficient group with
commuting difference endomorphisms.

It deliberately does not formalize Picard-Vessiot rings, a category of difference
modules, or the isomorphism theorem for actual modules. The ledger content here is:

* scalar cocycles are closed under multiplication and inverse;
* scalar coboundaries are scalar cocycles when the actions commute;
* coboundaries form a subgroup of cocycles;
* the quotient, the rank-one Picard group skeleton, is an abelian group.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The difference actions commute pairwise. -/
def commutingActions {ι G : Type*} [CommGroup G] (act : ι → G →* G) : Prop :=
  ∀ p q x, act p (act q x) = act q (act p x)

/-- The scalar rank-one cocycle condition `a_p * σ_p(a_q) = a_q * σ_q(a_p)`. -/
def scalarCocycle {ι G : Type*} [CommGroup G]
    (act : ι → G →* G) (a : ι → G) : Prop :=
  ∀ p q, a p * act p (a q) = a q * act q (a p)

lemma scalarCocycle_one {ι G : Type*} [CommGroup G] (act : ι → G →* G) :
    scalarCocycle act (1 : ι → G) := by
  intro p q
  simp

/-- Scalar rank-one cocycles are closed under tensor product/multiplication. -/
theorem scalarCocycle_mul {ι G : Type*} [CommGroup G] {act : ι → G →* G}
    {a b : ι → G} (ha : scalarCocycle act a) (hb : scalarCocycle act b) :
    scalarCocycle act (a * b) := by
  intro p q
  simp only [Pi.mul_apply, map_mul]
  calc
    (a p * b p) * (act p (a q) * act p (b q))
        = (a p * act p (a q)) * (b p * act p (b q)) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (a q * act q (a p)) * (b q * act q (b p)) := by rw [ha p q, hb p q]
    _ = (a q * b q) * (act q (a p) * act q (b p)) := by
            simp [mul_assoc, mul_left_comm, mul_comm]

/-- Scalar rank-one cocycles are closed under dual/inverse. -/
theorem scalarCocycle_inv {ι G : Type*} [CommGroup G] {act : ι → G →* G}
    {a : ι → G} (ha : scalarCocycle act a) :
    scalarCocycle act a⁻¹ := by
  intro p q
  simp only [Pi.inv_apply, map_inv]
  calc
    (a p)⁻¹ * (act p (a q))⁻¹
        = (a p * act p (a q))⁻¹ := by simp [mul_comm]
    _ = (a q * act q (a p))⁻¹ := by rw [ha p q]
    _ = (a q)⁻¹ * (act q (a p))⁻¹ := by simp [mul_comm]

/-- Rank-one scalar cocycles form an abelian group under pointwise multiplication. -/
def rankOneCocycles {ι G : Type*} [CommGroup G] (act : ι → G →* G) : Subgroup (ι → G) where
  carrier := scalarCocycle act
  one_mem' := scalarCocycle_one act
  mul_mem' := fun {_a} {_b} ha hb => scalarCocycle_mul ha hb
  inv_mem' := fun {_a} ha => scalarCocycle_inv ha

/-- The rank-one scalar coboundary `σ_p(h)/h`. -/
def rankOneCoboundary {ι G : Type*} [CommGroup G]
    (act : ι → G →* G) (h : G) : ι → G :=
  fun p => act p h * h⁻¹

/-- Coboundaries are cocycles when the difference actions commute. -/
theorem rankOneCoboundary_cocycle {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) (h : G) :
    scalarCocycle act (rankOneCoboundary act h) := by
  intro p q
  simp only [rankOneCoboundary, map_mul, map_inv]
  rw [hcomm p q h]
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- A coboundary regarded as a rank-one cocycle. -/
def rankOneCoboundaryCocycle {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) (h : G) : rankOneCocycles act :=
  ⟨rankOneCoboundary act h, rankOneCoboundary_cocycle hcomm h⟩

lemma rankOneCoboundaryCocycle_one {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) :
    rankOneCoboundaryCocycle hcomm (1 : G) = 1 := by
  ext p
  simp [rankOneCoboundaryCocycle, rankOneCoboundary]

/-- Scalar coboundaries multiply as `δ(hk)=δ(h)δ(k)`. -/
theorem rankOneCoboundaryCocycle_mul {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) (h k : G) :
    rankOneCoboundaryCocycle hcomm (h * k) =
      rankOneCoboundaryCocycle hcomm h * rankOneCoboundaryCocycle hcomm k := by
  ext p
  simp [rankOneCoboundaryCocycle, rankOneCoboundary, map_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Scalar coboundaries invert as `δ(h⁻¹)=δ(h)⁻¹`. -/
theorem rankOneCoboundaryCocycle_inv {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) (h : G) :
    rankOneCoboundaryCocycle hcomm h⁻¹ = (rankOneCoboundaryCocycle hcomm h)⁻¹ := by
  ext p
  simp [rankOneCoboundaryCocycle, rankOneCoboundary, map_inv, mul_comm]

/-- Rank-one coboundaries form a subgroup of the rank-one scalar cocycles. -/
def rankOneCoboundaries {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) : Subgroup (rankOneCocycles act) where
  carrier := fun a => ∃ h : G, a = rankOneCoboundaryCocycle hcomm h
  one_mem' := ⟨1, (rankOneCoboundaryCocycle_one hcomm).symm⟩
  mul_mem' := by
    rintro _ _ ⟨h, rfl⟩ ⟨k, rfl⟩
    exact ⟨h * k, (rankOneCoboundaryCocycle_mul hcomm h k).symm⟩
  inv_mem' := by
    rintro _ ⟨h, rfl⟩
    exact ⟨h⁻¹, (rankOneCoboundaryCocycle_inv hcomm h).symm⟩

/-- The rank-one Picard group skeleton: scalar cocycles modulo scalar coboundaries. -/
abbrev rankOnePicard {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) : Type _ :=
  rankOneCocycles act ⧸ rankOneCoboundaries hcomm

/-- The rank-one Picard quotient is an abelian group. -/
theorem rankOnePicard_commGroup {ι G : Type*} [CommGroup G]
    {act : ι → G →* G} (hcomm : commutingActions act) :
    Nonempty (CommGroup (rankOnePicard hcomm)) :=
  ⟨inferInstance⟩

end

end GaloisForLFunctions
