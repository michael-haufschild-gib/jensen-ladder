import GaloisForLFunctions.OrbitFreeness

/-!
# Finite-character frequencies for the diagonal Kronecker flow

This file formalizes the finite-character algebra behind
`constraint-not-flow-theorem.md` §1: a Fourier character with integer prime
exponent vector `m` has diagonal-flow frequency `Σ m_p log p`, axis modes have
frequency `k log p`, and unique factorization gives no nonzero finite
resonance. It does not formalize infinite torus spectral theory, Haar
equidistribution, or Hilbert-Pólya operators.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- Frequency of a finite integer Fourier character under the diagonal prime
Kronecker flow. -/
def primeLogFrequency (m : Nat.Primes →₀ ℤ) : ℝ :=
  m.sum fun p z => (z : ℝ) * Real.log (p : ℕ)

/-- Axis modes have frequency `k log p`. -/
theorem primeLogFrequency_single (p : Nat.Primes) (k : ℤ) :
    primeLogFrequency (Finsupp.single p k) = (k : ℝ) * Real.log (p : ℕ) := by
  simp [primeLogFrequency]

/-- The only finite integer character with zero diagonal-flow frequency is the
trivial character. -/
theorem primeLogFrequency_eq_zero_iff (m : Nat.Primes →₀ ℤ) :
    primeLogFrequency m = 0 ↔ m = 0 := by
  constructor
  · intro h
    exact log_prime_int_relation_eq_zero m (by simpa [primeLogFrequency] using h)
  · intro h
    simp [h, primeLogFrequency]

/-- Nontrivial finite characters have nonzero diagonal-flow frequency. -/
theorem primeLogFrequency_ne_zero (m : Nat.Primes →₀ ℤ) (hm : m ≠ 0) :
    primeLogFrequency m ≠ 0 := by
  intro h
  exact hm ((primeLogFrequency_eq_zero_iff m).mp h)

/-- A nonzero axis mode has nonzero prime frequency. -/
theorem primeLogFrequency_single_ne_zero (p : Nat.Primes) {k : ℤ} (hk : k ≠ 0) :
    primeLogFrequency (Finsupp.single p k) ≠ 0 := by
  apply primeLogFrequency_ne_zero
  intro h
  have hp := congrArg (fun f : Nat.Primes →₀ ℤ => f p) h
  exact hk (by simpa using hp)

end

end GaloisForLFunctions
