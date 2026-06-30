import GaloisForLFunctions.Core

/-!
# Smooth-number frequencies for finite auxiliary forms

`transcendence-theory-nonholonomic-functions.md` §8.1 observes that a finite
multi-`q` auxiliary form supported on primes `S` and exponent bound `N` pulls back to
a Dirichlet polynomial whose frequencies are exactly the `S`-smooth integers with
exponents at most `N`.

This file formalizes the finite unique-factorization skeleton of that statement:
exponent vectors on bundled primes, supported in `S` and bounded by `N`, are equivalent
to positive integers whose prime factorization is supported in `S` with all exponents at
most `N`. It does not formalize analytic pullbacks, vanishing orders, Siegel lemmas,
or any transcendence lower bound.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The prime-exponent vector of a natural number, indexed by bundled primes. -/
def primeExponentVector (n : ℕ) : Nat.Primes →₀ ℕ :=
  n.factorization.comapDomain (fun p : Nat.Primes => (p : ℕ)) (Subtype.val_injective.injOn)

@[simp] lemma primeExponentVector_apply (n : ℕ) (p : Nat.Primes) :
    primeExponentVector n p = n.factorization (p : ℕ) := by
  simp [primeExponentVector, Finsupp.comapDomain]

/-- Reconstructing a nonzero natural number from its bundled prime-exponent vector. -/
lemma primeProduct_primeExponentVector {n : ℕ} (hn : n ≠ 0) :
    primeProduct (primeExponentVector n) = n := by
  apply Nat.eq_of_factorization_eq
  · exact (primeProduct_pos (primeExponentVector n)).ne'
  · exact hn
  · intro q
    by_cases hq : q.Prime
    · let p : Nat.Primes := ⟨q, hq⟩
      have h := primeProduct_factorization (primeExponentVector n) p
      simpa [p] using h
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq,
        Nat.factorization_eq_zero_of_not_prime _ hq]

/-- The logarithm of a nonzero natural number is the finite sum of its prime
factorization exponents times the corresponding prime logarithms. This is the
formal version of `log k = Σ_p v_p(k) log p` used in the Stieltjes/continuation
block card. -/
theorem log_nat_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) =
      (primeExponentVector n).sum fun p k => (k : ℝ) * Real.log (p : ℕ) := by
  calc
    Real.log (n : ℝ) = Real.log (primeProduct (primeExponentVector n) : ℝ) := by
      rw [primeProduct_primeExponentVector hn]
    _ = (primeExponentVector n).sum fun p k => (k : ℝ) * Real.log (p : ℕ) :=
      log_primeProduct (primeExponentVector n)

/-- An exponent vector supported on a finite prime set `S`, with every exponent at most `N`. -/
def supportedBounded (S : Finset Nat.Primes) (N : ℕ) (m : Nat.Primes →₀ ℕ) : Prop :=
  m.support ⊆ S ∧ ∀ p : Nat.Primes, m p ≤ N

/-- Positive integers whose prime factors all lie in `S` with exponent at most `N`. -/
def isBoundedSmooth (S : Finset Nat.Primes) (N n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : Nat.Primes, n.factorization (p : ℕ) ≠ 0 →
    p ∈ S ∧ n.factorization (p : ℕ) ≤ N

lemma supportedBounded_primeExponentVector_of_isBoundedSmooth
    {S : Finset Nat.Primes} {N n : ℕ} (hn : isBoundedSmooth S N n) :
    supportedBounded S N (primeExponentVector n) := by
  constructor
  · intro p hp
    rw [Finsupp.mem_support_iff] at hp
    exact (hn.2 p hp).1
  · intro p
    by_cases hp : n.factorization (p : ℕ) = 0
    · simp [primeExponentVector_apply, hp]
    · exact (hn.2 p hp).2

lemma isBoundedSmooth_primeProduct_of_supportedBounded
    {S : Finset Nat.Primes} {N : ℕ} {m : Nat.Primes →₀ ℕ}
    (hm : supportedBounded S N m) :
    isBoundedSmooth S N (primeProduct m) := by
  constructor
  · exact (primeProduct_pos m).ne'
  · intro p hp
    rw [primeProduct_factorization] at hp ⊢
    exact ⟨hm.1 (Finsupp.mem_support_iff.mpr hp), hm.2 p⟩

/-- Bounded exponent vectors on `S` are exactly bounded `S`-smooth frequencies.

This is the unique-factorization content behind the draft's claim that a finite
multi-`q` auxiliary polynomial becomes a Dirichlet polynomial supported on bounded
smooth numbers after diagonal pullback. -/
def boundedExponentVectorEquivSmooth (S : Finset Nat.Primes) (N : ℕ) :
    {m : Nat.Primes →₀ ℕ // supportedBounded S N m} ≃
      {n : ℕ // isBoundedSmooth S N n} where
  toFun m := ⟨primeProduct m.1, isBoundedSmooth_primeProduct_of_supportedBounded m.2⟩
  invFun n :=
    ⟨primeExponentVector n.1, supportedBounded_primeExponentVector_of_isBoundedSmooth n.2⟩
  left_inv m := by
    apply Subtype.ext
    apply primeProduct_injective
    exact primeProduct_primeExponentVector (primeProduct_pos m.1).ne'
  right_inv n := by
    apply Subtype.ext
    exact primeProduct_primeExponentVector n.2.1

/-- A natural number is a bounded `S`-smooth frequency iff it is the prime product of a
bounded exponent vector supported on `S`. -/
theorem primeProduct_isBoundedSmooth_iff {S : Finset Nat.Primes} {N n : ℕ} :
    isBoundedSmooth S N n ↔
      ∃ m : Nat.Primes →₀ ℕ, supportedBounded S N m ∧ primeProduct m = n := by
  constructor
  · intro hn
    exact ⟨primeExponentVector n, supportedBounded_primeExponentVector_of_isBoundedSmooth hn,
      primeProduct_primeExponentVector hn.1⟩
  · rintro ⟨m, hm, rfl⟩
    exact isBoundedSmooth_primeProduct_of_supportedBounded hm

lemma cpow_nat_prime_power (p : Nat.Primes) (k : ℕ) (s : ℂ) :
    ((((p : ℕ) ^ k : ℕ) : ℂ)) ^ (-s) = (((p : ℕ) : ℂ) ^ (-s)) ^ k := by
  rw [Nat.cast_pow]
  rw [← Complex.cpow_nat_mul]
  rw [Complex.natCast_cpow_natCast_mul]

/-- A diagonal monomial in prime Bohr coordinates has the Dirichlet frequency
given by its finite prime product. -/
theorem diagonalMonomial_eq_frequency (m : Nat.Primes →₀ ℕ) (s : ℂ) :
    m.prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k) =
      ((primeProduct m : ℕ) : ℂ) ^ (-s) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp [primeProduct]
  | single_add a b f haf hb ih =>
      have hleft :
          (Finsupp.single a b + f).prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k) =
            (((a : ℕ) : ℂ) ^ (-s)) ^ b *
              f.prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k) := by
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      have hprod : primeProduct (Finsupp.single a b + f) = (a : ℕ) ^ b * primeProduct f := by
        unfold primeProduct
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      rw [hleft, ih, hprod]
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      rw [cpow_nat_prime_power]

/-- A finite auxiliary form in prime Bohr coordinates pulls back on the diagonal to a
finite Dirichlet polynomial with frequencies `primeProduct m`. -/
theorem diagonalAuxiliaryForm_eq_dirichletPolynomial
    (P : (Nat.Primes →₀ ℕ) →₀ ℂ) (s : ℂ) :
    P.sum (fun m c => c * m.prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k)) =
      P.sum (fun m c => c * ((primeProduct m : ℕ) : ℂ) ^ (-s)) := by
  refine Finsupp.sum_congr ?_
  intro m _
  rw [diagonalMonomial_eq_frequency]

end

end GaloisForLFunctions
