import GaloisForLFunctions.KroneckerFlow

/-!
# Finite Bohr-character generator identities

This file formalizes the finite algebraic skeleton of
`archimedean-generator-axis-mode.md`: prime-coordinate scaling acts diagonally
on finitely supported Bohr characters, and products of characters add their
exponent vectors. It deliberately does not formalize infinite torus analysis,
unbounded differential operators, or global holonomy.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- A finitely supported integer Bohr character on a commutative multiplicative
group. For the prime torus, this is `e_m(x)=∏_p x_p^{m_p}`. -/
def bohrCharacter {ι G : Type*} [CommGroup G] (m : ι →₀ ℤ) (x : ι → G) : G :=
  m.prod fun p n => x p ^ n

/-- Scale one coordinate of a torus point. For a prime lane this is
`x_p ↦ c*x_p` with all other coordinates unchanged. -/
def scaleCoordinate {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (p : ι) (c : G) (x : ι → G) : ι → G :=
  Function.update x p (c * x p)

/-- Scale every coordinate of a torus point. The finite-support condition on
Bohr characters makes the resulting product action finite on each character. -/
def scaleAllCoordinates {ι G : Type*} [CommGroup G] (c : ι → G) (x : ι → G) : ι → G :=
  fun i => c i * x i

/-- The trivial exponent vector gives the trivial Bohr character. -/
theorem bohrCharacter_zero {ι G : Type*} [CommGroup G] (x : ι → G) :
    bohrCharacter (0 : ι →₀ ℤ) x = 1 := by
  simp [bohrCharacter]

/-- Products of Bohr characters add exponent vectors:
`e_{m+n}=e_m*e_n`. This is the finite algebraic identity behind the card's
statement that combination modes arise from the ring product. -/
theorem bohrCharacter_add {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (m n : ι →₀ ℤ) (x : ι → G) :
    bohrCharacter (m + n) x = bohrCharacter m x * bohrCharacter n x := by
  unfold bohrCharacter
  rw [Finsupp.prod_add_index]
  · intro a
    simp
  · intro a _ b c
    rw [zpow_add]

/-- Scaling the `p` coordinate acts diagonally on a Bohr character:
`e_m(..., c*x_p, ...) = c^{m_p} e_m(x)`. For `c=p^{-1}` this is the finite
form of `σ_p e_m = p^{-m_p} e_m`. -/
theorem bohrCharacter_scaleCoordinate {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (m : ι →₀ ℤ) (p : ι) (c : G) (x : ι → G) :
    bohrCharacter m (scaleCoordinate p c x) = c ^ (m p) * bohrCharacter m x := by
  classical
  unfold bohrCharacter scaleCoordinate
  rw [Finsupp.prod, Finsupp.prod]
  by_cases hp : p ∈ m.support
  · rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hp]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hp]
    simp only [Function.update_self]
    have hprod :
        (∏ q ∈ m.support \ {p}, Function.update x p (c * x p) q ^ m q) =
          ∏ q ∈ m.support \ {p}, x q ^ m q := by
      refine Finset.prod_congr rfl ?_
      intro q hq
      have hqne : q ≠ p := by
        have hnot : q ∉ ({p} : Finset ι) := (Finset.mem_sdiff.mp hq).2
        exact Finset.notMem_singleton.mp hnot
      simp [Function.update_of_ne hqne]
    rw [hprod]
    rw [mul_zpow]
    group
  · have hmp : m p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hmp]
    refine Finset.prod_congr rfl ?_
    intro q hq
    have hqne : q ≠ p := by
      intro h
      subst h
      exact hp hq
    simp [Function.update_of_ne hqne]

/-- Scaling all coordinates acts diagonally on a finite Bohr character. This is
the finite-support algebra behind applying a family of commuting coordinate
dilations all at once. -/
theorem bohrCharacter_scaleAllCoordinates {ι G : Type*} [CommGroup G]
    (m : ι →₀ ℤ) (c x : ι → G) :
    bohrCharacter m (scaleAllCoordinates c x) = bohrCharacter m c * bohrCharacter m x := by
  classical
  unfold bohrCharacter scaleAllCoordinates
  rw [Finsupp.prod, Finsupp.prod, Finsupp.prod]
  simp_rw [mul_zpow]
  rw [Finset.prod_mul_distrib]

/-- Coordinate scalings commute. This is the finite torus-map skeleton behind
the commutation of prime dilations. -/
theorem scaleCoordinate_commute {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (p q : ι) (c d : G) (x : ι → G) :
    scaleCoordinate p c (scaleCoordinate q d x) =
      scaleCoordinate q d (scaleCoordinate p c x) := by
  funext r
  unfold scaleCoordinate
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> subst_vars <;> simp [mul_left_comm] at *

/-- Coordinatewise scalings commute with each other. -/
theorem scaleAllCoordinates_commute {ι G : Type*} [CommGroup G]
    (c d : ι → G) (x : ι → G) :
    scaleAllCoordinates c (scaleAllCoordinates d x) =
      scaleAllCoordinates d (scaleAllCoordinates c x) := by
  funext r
  simp [scaleAllCoordinates, mul_left_comm]

/-- A single coordinate scaling commutes with a simultaneous coordinatewise
scaling. This is the finite coordinate-map form of `[sigma_infty, sigma_p]=0`
on the prime-coordinate base. -/
theorem scaleCoordinate_scaleAllCoordinates_commute {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (p : ι) (d : G) (c : ι → G) (x : ι → G) :
    scaleCoordinate p d (scaleAllCoordinates c x) =
      scaleAllCoordinates c (scaleCoordinate p d x) := by
  funext r
  unfold scaleCoordinate scaleAllCoordinates
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp [mul_left_comm] at *

/-- The nonzero complex unit attached to a prime. -/
def primeComplexUnit (p : Nat.Primes) : ℂˣ :=
  Units.mk0 (((p : ℕ) : ℂ)) (by exact_mod_cast p.2.ne_zero)

/-- The simultaneous square of the prime dilations, `x_p ↦ p^{-2} x_p`, as a
coordinatewise scale on the prime torus. -/
def archimedeanSquareScale : Nat.Primes → ℂˣ :=
  fun p => (primeComplexUnit p) ^ (-2 : ℤ)

/-- Finite-support product-formula skeleton: applying the simultaneous square
of all prime dilations to a Bohr character multiplies it by the finite product
of the prime-square scale factors on its support. This is the formal finite
character form of `sigma_infty|_R = product_p sigma_p^2` on the base. -/
theorem bohrCharacter_archimedeanSquareScale (m : Nat.Primes →₀ ℤ) (x : Nat.Primes → ℂˣ) :
    bohrCharacter m (scaleAllCoordinates archimedeanSquareScale x) =
      bohrCharacter m archimedeanSquareScale * bohrCharacter m x := by
  exact bohrCharacter_scaleAllCoordinates m archimedeanSquareScale x

/-- A two-axis exponent vector with nonzero coefficients at two distinct axes
has exactly those two axes as support. This is the finite algebraic meaning of a
genuine two-prime combination mode. -/
theorem twoAxisMode_support_eq {ι : Type*} [DecidableEq ι]
    {p q : ι} (hpq : p ≠ q) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Finsupp.single p a + Finsupp.single q b).support = ({p, q} : Finset ι) := by
  ext r
  by_cases hrp : r = p
  · subst hrp
    simp [hpq, ha]
  · by_cases hrq : r = q
    · subst hrq
      simp [hpq, hb]
    · simp [hrp, hrq]

/-- The product of two axis Bohr characters is the corresponding two-axis
combination mode. -/
theorem bohrCharacter_twoAxis_product {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (p q : ι) (a b : ℤ) (x : ι → G) :
    bohrCharacter (Finsupp.single p a + Finsupp.single q b) x =
      bohrCharacter (Finsupp.single p a) x * bohrCharacter (Finsupp.single q b) x := by
  exact bohrCharacter_add (Finsupp.single p a) (Finsupp.single q b) x

/-- A two-axis mode with a nonzero coefficient on the first axis is nontrivial. -/
theorem twoAxisMode_ne_zero {ι : Type*} [DecidableEq ι]
    {p q : ι} (hpq : p ≠ q) {a b : ℤ} (ha : a ≠ 0) :
    Finsupp.single p a + Finsupp.single q b ≠ (0 : ι →₀ ℤ) := by
  intro h
  have hp := congrArg (fun f : ι →₀ ℤ => f p) h
  simp [hpq, ha] at hp

end

end GaloisForLFunctions
