import GaloisForLFunctions.Core

/-!
# Finite Morita gamma recurrence

This file formalizes the finite integer-algebra skeleton of the Morita
`Gamma_p` recurrence from
`docs/drafts/pipeline/2-fully-proven/per-place-source-a-gamma-carriers.md`.

For a prime `p`, define the positive-integer values by the finite product
`(-1)^n * prod_{j<n, p not dividing j} j`. Since every prime divides `0`,
this is the same finite product as `0 < j < n, p not dividing j`.

The file does not formalize p-adic analytic continuation, the Source-A grade,
the multiplier dichotomy, or any complex/p-adic comparison.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- The finite product part of Morita's positive-integer `Gamma_p` formula. -/
def moritaGammaProduct (p : Nat.Primes) (n : ℕ) : ℤ :=
  ∏ j ∈ (Finset.range n).filter (fun j => ¬ (p : ℕ) ∣ j), (j : ℤ)

/-- The finite positive-integer Morita `Gamma_p` values used by the recurrence. -/
def moritaGammaFinite (p : Nat.Primes) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * moritaGammaProduct p n

/-- If `p ∣ n`, the new index `n` is excluded from the filtered product. -/
lemma moritaGammaProduct_succ_of_dvd (p : Nat.Primes) {n : ℕ} (h : (p : ℕ) ∣ n) :
    moritaGammaProduct p (n + 1) = moritaGammaProduct p n := by
  unfold moritaGammaProduct
  rw [Finset.range_add_one]
  simp [Finset.filter_insert, h]

/-- If `p ∤ n`, the new index `n` contributes the factor `n`. -/
lemma moritaGammaProduct_succ_of_not_dvd (p : Nat.Primes) {n : ℕ} (h : ¬ (p : ℕ) ∣ n) :
    moritaGammaProduct p (n + 1) = (n : ℤ) * moritaGammaProduct p n := by
  unfold moritaGammaProduct
  rw [Finset.range_add_one]
  simp [Finset.filter_insert, h]

/-- Morita recurrence branch at indices divisible by `p`: `Gamma_p(n+1)=-Gamma_p(n)`. -/
lemma moritaGammaFinite_succ_of_dvd (p : Nat.Primes) {n : ℕ} (h : (p : ℕ) ∣ n) :
    moritaGammaFinite p (n + 1) = -moritaGammaFinite p n := by
  unfold moritaGammaFinite
  rw [moritaGammaProduct_succ_of_dvd p h]
  rw [pow_succ]
  ring

/-- Morita recurrence branch away from `p`: `Gamma_p(n+1)=-n*Gamma_p(n)`. -/
lemma moritaGammaFinite_succ_of_not_dvd (p : Nat.Primes) {n : ℕ}
    (h : ¬ (p : ℕ) ∣ n) :
    moritaGammaFinite p (n + 1) = -(n : ℤ) * moritaGammaFinite p n := by
  unfold moritaGammaFinite
  rw [moritaGammaProduct_succ_of_not_dvd p h]
  rw [pow_succ]
  ring

/-- Combined finite Morita recurrence:
`Gamma_p(n+1) = -Gamma_p(n)` if `p ∣ n`, and
`Gamma_p(n+1) = -n*Gamma_p(n)` otherwise. -/
theorem moritaGammaFinite_succ (p : Nat.Primes) (n : ℕ) :
    moritaGammaFinite p (n + 1) =
      (if (p : ℕ) ∣ n then (-1 : ℤ) else -(n : ℤ)) * moritaGammaFinite p n := by
  by_cases h : (p : ℕ) ∣ n
  · simp [h, moritaGammaFinite_succ_of_dvd p h]
  · simp [h, moritaGammaFinite_succ_of_not_dvd p h]

end

end GaloisForLFunctions
