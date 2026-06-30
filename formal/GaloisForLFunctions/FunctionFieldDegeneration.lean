import GaloisForLFunctions.Resonance

/-!
# Function-field degree collapse

This file formalizes the finite-support algebra behind the function-field
degeneration card: once every place multiplier is a power of one base, relations
are exactly the kernel of the degree map, and a degree-one place makes the
quotient rank one.

The analytic/geometric inputs on the card (G3/Lipshitz/Weil rationality) are not
encoded here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Minimal formal data for the `F_q(t)`/constant-field-reduced case: a closed
place set with an integer degree map and a chosen degree-one place. -/
structure FunctionFieldDegreeData where
  Place : Type
  degree : Place → ℤ
  degreeOnePlace : Place
  degree_degreeOnePlace : degree degreeOnePlace = 1

/-- The finite-support degree map `∑_v m_v deg(v)`. -/
def ffDegreeMap (K : FunctionFieldDegreeData) :
    (K.Place →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ fun v => LinearMap.toSpanSingleton ℤ ℤ (K.degree v)

/-- The function-field relation lattice: finite integer combinations of places
with total degree zero. -/
def ffRelationLattice (K : FunctionFieldDegreeData) :
    Submodule ℤ (K.Place →₀ ℤ) :=
  (ffDegreeMap K).ker

/-- The degree map is the displayed finite sum from the paper proof. -/
theorem ffDegreeMap_apply (K : FunctionFieldDegreeData) (m : K.Place →₀ ℤ) :
    ffDegreeMap K m = m.sum (fun v n => n * K.degree v) := by
  rw [ffDegreeMap]
  simp [Finsupp.lsum, LinearMap.toSpanSingleton]

/-- `Λ_ff = ker(deg)`: membership in the relation lattice is exactly vanishing
total degree. -/
theorem ffRelationLattice_mem_iff (K : FunctionFieldDegreeData) (m : K.Place →₀ ℤ) :
    m ∈ ffRelationLattice K ↔ m.sum (fun v n => n * K.degree v) = 0 := by
  rw [ffRelationLattice, LinearMap.mem_ker, ffDegreeMap_apply]

/-- A degree-one place makes the degree map onto `ℤ`. -/
theorem ffDegreeMap_surjective (K : FunctionFieldDegreeData) :
    Function.Surjective (ffDegreeMap K) := by
  intro z
  refine ⟨Finsupp.single K.degreeOnePlace z, ?_⟩
  rw [ffDegreeMap]
  simp [Finsupp.lsum, LinearMap.toSpanSingleton, K.degree_degreeOnePlace]

/-- The image of the degree map is all of `ℤ`. -/
theorem ffDegreeMap_range_eq_top (K : FunctionFieldDegreeData) :
    (ffDegreeMap K).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact ffDegreeMap_surjective K

/-- First-isomorphism form of the collapse: quotient by `Λ_ff` is the one
degree direction. -/
def ffDegreeQuotientEquivInt (K : FunctionFieldDegreeData) :
    ((K.Place →₀ ℤ) ⧸ ffRelationLattice K) ≃ₗ[ℤ] ℤ :=
  LinearMap.quotKerEquivOfSurjective (ffDegreeMap K) (ffDegreeMap_surjective K)

/-- `corank(Λ_ff) = 1`, formalized as the rank of the quotient by the relation
lattice. -/
theorem ffRelationLattice_corank_eq_one (K : FunctionFieldDegreeData) :
    Module.rank ℤ ((K.Place →₀ ℤ) ⧸ ffRelationLattice K) = 1 := by
  rw [LinearEquiv.rank_eq (ffDegreeQuotientEquivInt K), Module.rank_self]

end

end GaloisForLFunctions
