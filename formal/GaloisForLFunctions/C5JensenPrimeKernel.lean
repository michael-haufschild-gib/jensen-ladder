import Mathlib

/-!
# C5 Jensen prime kernel: von Mangoldt coefficient anchor (Tier A)

This file formalizes the elementary arithmetic coefficient calculation from
`docs/drafts/pipeline/2-fully-proven/c5-jensen-prime-kernel.md`.

In the prime part of `log ζ`, the coefficient attached to frequency `log n` is
`Λ(n) n^{-1/2} / log n`. For a prime `p`, this is `p^{-1/2}` because
`Λ(p)=log p`; for a prime power `p^k`, it is `p^{-k/2}/k`.

No Pólya-Laguerre, Jensen-polynomial, explicit-formula regularization, or
root-perturbation statement is formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped ArithmeticFunction

/-- The real coefficient magnitude `Λ(n)/log n · n^{-1/2}` in the prime part of `log ζ`. -/
def logZetaPrimeCoeff (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- For a prime `p`, the `log ζ` coefficient is `p^{-1/2}`. -/
theorem logZetaPrimeCoeff_prime (p : Nat.Primes) :
    logZetaPrimeCoeff (p : ℕ) = ((p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hpPrime : Nat.Prime (p : ℕ) := p.2
  have hpgt : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hpPrime.one_lt
  have hlogne : Real.log ((p : ℕ) : ℝ) ≠ 0 := (Real.log_pos hpgt).ne'
  unfold logZetaPrimeCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
  field_simp [hlogne]

/-- For a prime power `p^k`, the `log ζ` coefficient is `p^{-k/2}/k`. -/
theorem logZetaPrimeCoeff_primePower (p : Nat.Primes) {k : ℕ} (hk : k ≠ 0) :
    logZetaPrimeCoeff ((p : ℕ) ^ k) = ((p : ℝ) ^ (-(k : ℝ) / 2)) / (k : ℝ) := by
  have hpPrime : Nat.Prime (p : ℕ) := p.2
  have hpgt : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hpPrime.one_lt
  have hlogp_ne : Real.log ((p : ℕ) : ℝ) ≠ 0 := (Real.log_pos hpgt).ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hp_nonneg : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  unfold logZetaPrimeCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
  rw [Nat.cast_pow, Real.log_pow]
  have hrpow : (((p : ℕ) : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = ((p : ℝ) ^ (-(k : ℝ) / 2)) := by
    rw [← Real.rpow_natCast ((p : ℕ) : ℝ) k]
    rw [← Real.rpow_mul hp_nonneg]
    congr 1
    ring
  rw [hrpow]
  field_simp [hlogp_ne, hkR]

end

end GaloisForLFunctions
