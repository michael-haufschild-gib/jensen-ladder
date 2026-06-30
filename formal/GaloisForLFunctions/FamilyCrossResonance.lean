import GaloisForLFunctions.BohrGenerators
import GaloisForLFunctions.ZeroEstimate

/-!
# Family cross-resonance modulus split

This file formalizes the finite algebraic core of
`docs/drafts/pipeline/2-fully-proven/family-dss-gsh.md` §R1.

A family resonance has a family-dependent twist and a shared prime scale. The
finite product splits into a twist product and a shared-scale product whose
exponent vector is the per-prime family sum. Unique factorization then forces
that per-prime balance to vanish whenever the positive prime-product modulus
part is trivial.

This file does not formalize Dirichlet characters, cyclotomic Galois theory,
GSH, zero statistics, or the value-lift/F1 apex.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- Sum the exponent vectors across a finite family. -/
def familyExponentSum {ι κ : Type*} [Fintype ι] (m : ι → κ →₀ ℤ) : κ →₀ ℤ :=
  ∑ i, m i

@[simp] theorem familyExponentSum_apply {ι κ : Type*} [Fintype ι]
    (m : ι → κ →₀ ℤ) (k : κ) :
    familyExponentSum m k = ∑ i, m i k := by
  simp [familyExponentSum]

/-- Bohr characters turn finite sums of exponent vectors into products. -/
lemma bohrCharacter_finset_sum {ι κ G : Type*} [DecidableEq κ] [CommGroup G]
    (s : Finset ι) (m : ι → κ →₀ ℤ) (x : κ → G) :
    bohrCharacter (∑ i ∈ s, m i) x = ∏ i ∈ s, bohrCharacter (m i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bohrCharacter_zero]
  | insert a s ha ih =>
      simp [ha, bohrCharacter_add, ih]

/-- Family form of `bohrCharacter_finset_sum`. -/
lemma bohrCharacter_familyExponentSum {ι κ G : Type*}
    [Fintype ι] [DecidableEq κ] [CommGroup G]
    (m : ι → κ →₀ ℤ) (x : κ → G) :
    bohrCharacter (familyExponentSum m) x = ∏ i, bohrCharacter (m i) x := by
  classical
  simpa [familyExponentSum] using
    (bohrCharacter_finset_sum (s := (Finset.univ : Finset ι)) (m := m) (x := x))

/-- A finite family product with one shared scale and one family-dependent twist. -/
def familyTwistedProduct {ι κ G : Type*} [Fintype ι] [CommGroup G]
    (twist : ι → κ → G) (scale : κ → G) (m : ι → κ →₀ ℤ) : G :=
  ∏ i, bohrCharacter (m i) (fun k => twist i k * scale k)

/-- Split a finite family product into its twist part and shared-scale modulus part. -/
theorem familyTwistedProduct_split {ι κ G : Type*}
    [Fintype ι] [DecidableEq κ] [CommGroup G]
    (twist : ι → κ → G) (scale : κ → G) (m : ι → κ →₀ ℤ) :
    familyTwistedProduct twist scale m =
      (∏ i, bohrCharacter (m i) (twist i)) * bohrCharacter (familyExponentSum m) scale := by
  classical
  unfold familyTwistedProduct
  have hterm : ∀ i,
      bohrCharacter (m i) (fun k => twist i k * scale k) =
        bohrCharacter (m i) (twist i) * bohrCharacter (m i) scale := by
    intro i
    have hscale := bohrCharacter_scaleAllCoordinates (m i) scale (twist i)
    have hfun : (fun k => twist i k * scale k) = scaleAllCoordinates scale (twist i) := by
      funext k
      simp [scaleAllCoordinates, mul_comm]
    rw [hfun, hscale, mul_comm]
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  rw [← bohrCharacter_familyExponentSum]

/-- Per-prime exponent balance across a finite family. -/
def familyPrimeBalance {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℤ :=
  familyExponentSum m

@[simp] theorem familyPrimeBalance_apply {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ) (p : Nat.Primes) :
    familyPrimeBalance m p = ∑ i, m i p := by
  simp [familyPrimeBalance, familyExponentSum]

/-- Unique factorization forces the family prime-balance vector to vanish once
its positive and negative prime products agree. -/
theorem familyPrimeBalance_eq_zero_of_primeProduct_eq {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ)
    (h : primeProduct (positivePart (familyPrimeBalance m)) =
      primeProduct (negativePart (familyPrimeBalance m))) :
    familyPrimeBalance m = 0 := by
  exact positive_negative_eq_zero_of_primeProduct_eq h

/-- Pointwise version: the exponent sum over the family vanishes at every prime. -/
theorem familyPrimeBalance_apply_eq_zero_of_primeProduct_eq {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ)
    (h : primeProduct (positivePart (familyPrimeBalance m)) =
      primeProduct (negativePart (familyPrimeBalance m)))
    (p : Nat.Primes) :
    ∑ i, m i p = 0 := by
  have hbal := familyPrimeBalance_eq_zero_of_primeProduct_eq m h
  have hp := congrArg (fun f : Nat.Primes →₀ ℤ => f p) hbal
  simpa [familyPrimeBalance] using hp

/-- Log-frequency form of the same modulus conclusion. -/
theorem familyPrimeBalance_eq_zero_of_primeLogFrequency_eq_zero {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ)
    (h : primeLogFrequency (familyPrimeBalance m) = 0) :
    familyPrimeBalance m = 0 := by
  exact (primeLogFrequency_eq_zero_iff (familyPrimeBalance m)).mp h

/-- Pointwise log-frequency form of the family prime-balance conclusion. -/
theorem familyPrimeBalance_apply_eq_zero_of_primeLogFrequency_eq_zero {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ)
    (h : primeLogFrequency (familyPrimeBalance m) = 0)
    (p : Nat.Primes) :
    ∑ i, m i p = 0 := by
  have hbal := familyPrimeBalance_eq_zero_of_primeLogFrequency_eq_zero m h
  have hp := congrArg (fun f : Nat.Primes →₀ ℤ => f p) hbal
  simpa [familyPrimeBalance] using hp

end

end GaloisForLFunctions
