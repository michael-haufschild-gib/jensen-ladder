import Mathlib

/-!
# First Koszul differentials for difference cohomology

`multi-q-difference-galois-foundations.md` §20 identifies difference cohomology with the
Koszul complex on the commuting operators `(σ_p - 1)`. This file formalizes the first
two differentials for an arbitrary additive coefficient group with commuting additive
endomorphisms:

* `d₀ x = (σ_p x - x)_p`;
* `d₁ c = ((σ_p - 1)c_q - (σ_q - 1)c_p)_{p,q}`;
* `d₀ x = 0` iff `x` is jointly invariant;
* additive coboundaries are additive 1-cocycles, equivalently `d₁ ∘ d₀ = 0`.

It deliberately does not formalize group cohomology, the quotient defining `H¹`, exterior
powers, cup products, the infinite prime-lattice limit, or the `H²` curvature obstruction.
Those remain draft-side structures until a larger formal cohomology framework is built.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The additive difference actions commute pairwise. -/
def commutingAdditiveActions {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) : Prop :=
  ∀ p q x, act p (act q x) = act q (act p x)

/-- Joint invariants for an additive family of difference actions. -/
def additiveInvariant {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (x : M) : Prop :=
  ∀ p, act p x = x

/-- The first Koszul differential `d₀ x = (σ_p x - x)_p`. -/
def koszulD0 {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (x : M) : ι → M :=
  fun p => act p x - x

/-- The kernel of the first Koszul differential is exactly the joint invariant subspace. -/
theorem koszulD0_eq_zero_iff_invariant {ι M : Type*} [AddCommGroup M]
    (act : ι → M →+ M) (x : M) :
    koszulD0 act x = 0 ↔ additiveInvariant act x := by
  constructor
  · intro h p
    exact sub_eq_zero.mp (congr_fun h p)
  · intro h
    ext p
    exact sub_eq_zero.mpr (h p)

/-- Additive 1-cocycles: `(σ_p - 1)c_q = (σ_q - 1)c_p`. -/
def additiveCocycle {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (c : ι → M) :
    Prop :=
  ∀ p q, act p (c q) - c q = act q (c p) - c p

/-- The second Koszul differential on a 1-cochain. -/
def koszulD1 {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (c : ι → M) :
    ι → ι → M :=
  fun p q => (act p (c q) - c q) - (act q (c p) - c p)

/-- Vanishing of the second Koszul differential is exactly the additive 1-cocycle condition. -/
theorem koszulD1_eq_zero_iff_additiveCocycle {ι M : Type*} [AddCommGroup M]
    (act : ι → M →+ M) (c : ι → M) :
    (∀ p q, koszulD1 act c p q = 0) ↔ additiveCocycle act c := by
  constructor
  · intro h p q
    exact sub_eq_zero.mp (h p q)
  · intro h p q
    exact sub_eq_zero.mpr (h p q)

/-- The additive Koszul coboundary `δh = (σ_p h - h)_p`. -/
def koszulCoboundary {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (h : M) :
    ι → M :=
  koszulD0 act h

/-- Additive coboundaries are additive 1-cocycles when the difference actions commute. -/
theorem koszulCoboundary_cocycle {ι M : Type*} [AddCommGroup M]
    {act : ι → M →+ M} (hcomm : commutingAdditiveActions act) (h : M) :
    additiveCocycle act (koszulCoboundary act h) := by
  intro p q
  dsimp [koszulCoboundary, koszulD0]
  rw [map_sub, map_sub, hcomm p q h]
  abel

/-- The first two Koszul differentials compose to zero: `d₁ (d₀ h) = 0`. -/
theorem koszulD1_koszulD0_eq_zero {ι M : Type*} [AddCommGroup M]
    {act : ι → M →+ M} (hcomm : commutingAdditiveActions act) (h : M) :
    ∀ p q, koszulD1 act (koszulD0 act h) p q = 0 := by
  exact (koszulD1_eq_zero_iff_additiveCocycle act (koszulD0 act h)).mpr
    (by simpa [koszulCoboundary] using koszulCoboundary_cocycle hcomm h)

/-- The alternating binomial count underlying the finite Koszul Euler characteristic. -/
theorem koszul_alternating_choose_sum_eq_zero (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ)) = 0 := by
  have h := add_pow (-1 : ℤ) 1 n
  have hzero : ((-1 : ℤ) + 1) ^ n = 0 := by
    simp [Nat.ne_of_gt hn]
  rw [hzero] at h
  simpa [mul_assoc] using h.symm

/-- The finite Koszul rank Euler characteristic vanishes for a nonempty finite operator set:
`dim M · Σ_i (-1)^i choose(n,i) = 0`. This is only the rank count of the complex terms, not a
claim about individual cohomology dimensions. -/
theorem koszul_euler_characteristic_eq_zero (n dimM : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ) * (dimM : ℤ)) = 0 := by
  rw [← Finset.sum_mul]
  rw [koszul_alternating_choose_sum_eq_zero n hn]
  simp

end

end GaloisForLFunctions
