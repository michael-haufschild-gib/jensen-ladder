import Mathlib

/-!
# The non-circularity firewall: primes have no exact log-resonance (unique factorization)

This module formalizes the *arithmetic heart* of the fake-family / non-circularity
firewall used throughout the J-program and the T3/T5 construction plan
(`docs/rh/dyson_smooth_number_resonance_core_20260617.md`, facts F-SN-1/F-SN-2):

> The prime field has **no nontrivial exact resonance**: the only integer linear
> relation `∑ aᵢ log pᵢ = 0` among logarithms of distinct primes is the trivial
> one.  Equivalently, a product of powers of distinct primes determines its
> exponents (unique factorization).

**Why this is the firewall.** In the Weil explicit formula the prime side is an
almost-periodic function with frequencies `{log p}`.  Its `T→∞` joint moments are
exactly Gaussian (Wick) *because* the only surviving frequencies `∑ εⱼ log pᵢⱼ = 0`
are the trivial pairings — and that triviality is precisely
`log_prime_resonance_free` below.  A Davenport–Heilbronn / Beurling fake replaces
`{log p}` by generalized-prime frequencies that need **not** be ℚ-independent: a
Beurling system can satisfy an exact multiplicative relation `gᵢgⱼ = gₖgₗ`, i.e. a
*nontrivial* resonance, which produces non-Wick moments, a non-Gaussian field, and
off-line zeros.  So the separator "real primes vs fakes" **is** unique
factorization — this is what makes the fake-family referee non-circular.

Evidence class: elementary number theory (unique factorization + `exp`/`log`),
axiom-clean.  It does NOT prove RH; it formalizes the non-circularity mechanism.
-/

namespace JensenLadder
namespace PrimeResonanceFreeness

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Unique factorization, indexed form.** A product of powers of *distinct*
primes determines the exponent vector: `∏ pᵢ^{aᵢ} = ∏ pᵢ^{bᵢ} → a = b`. -/
theorem prime_pow_prod_inj (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {a b : ι → ℕ}
    (h : ∏ i, p i ^ a i = ∏ i, p i ^ b i) : a = b := by
  funext j
  have key : ∀ c : ι → ℕ, (∏ i, p i ^ c i).factorization (p j) = c j := by
    intro c
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero)]
    rw [Finsupp.finsetSum_apply]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization, Finsupp.single_apply])]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun hpij => hij (hinj hpij)), mul_zero]
    · intro hj; exact absurd (mem_univ j) hj
  have := congrArg (fun n => n.factorization (p j)) h
  simpa [key a, key b] using this

/-- **No exact resonance among `{log p}` (the non-circularity firewall).**
For distinct primes `pᵢ`, the only integer linear relation `∑ aᵢ log pᵢ = 0` is
trivial (`a = 0`).  This is ℚ-linear independence of `{log p}` = unique
factorization, the property the Davenport–Heilbronn/Beurling fakes lack. -/
theorem log_prime_resonance_free (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {a : ι → ℤ}
    (h : ∑ i, (a i : ℝ) * Real.log (p i) = 0) : a = 0 := by
  set ap : ι → ℕ := fun i => (a i).toNat with hap
  set am : ι → ℕ := fun i => (-(a i)).toNat with ham
  have hppos : ∀ i, (0:ℝ) < p i := fun i => by exact_mod_cast (hp i).pos
  have hsplit : ∀ i, (a i : ℝ) = (ap i : ℝ) - (am i : ℝ) := by
    intro i
    have h0 := Int.toNat_sub_toNat_neg (a i)
    have h1 : ((ap i : ℤ) - (am i : ℤ) : ℝ) = (a i : ℝ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) h0
    push_cast at h1 ⊢; linarith [h1]
  have heq : (∑ i, (ap i : ℝ) * Real.log (p i)) = (∑ i, (am i : ℝ) * Real.log (p i)) := by
    have hz : ∑ i, ((ap i : ℝ) - (am i : ℝ)) * Real.log (p i) = 0 := by
      rw [← h]; exact Finset.sum_congr rfl (fun i _ => by rw [hsplit i])
    simp only [sub_mul, Finset.sum_sub_distrib] at hz
    linarith [hz]
  have hexp : ∏ i, (p i : ℝ) ^ ap i = ∏ i, (p i : ℝ) ^ am i := by
    have lhs : ∏ i, (p i : ℝ) ^ ap i = Real.exp (∑ i, (ap i : ℝ) * Real.log (p i)) := by
      rw [Real.exp_sum]; exact Finset.prod_congr rfl (fun i _ => by
        rw [Real.exp_nat_mul, Real.exp_log (hppos i)])
    have rhs : ∏ i, (p i : ℝ) ^ am i = Real.exp (∑ i, (am i : ℝ) * Real.log (p i)) := by
      rw [Real.exp_sum]; exact Finset.prod_congr rfl (fun i _ => by
        rw [Real.exp_nat_mul, Real.exp_log (hppos i)])
    rw [lhs, rhs, heq]
  have hnat : ∏ i, p i ^ ap i = ∏ i, p i ^ am i := by
    have hcast : ((∏ i, p i ^ ap i : ℕ) : ℝ) = ((∏ i, p i ^ am i : ℕ) : ℝ) := by
      push_cast; exact hexp
    exact_mod_cast hcast
  have hapam : ap = am := prime_pow_prod_inj p hp hinj hnat
  funext i
  have hi : (ap i : ℤ) - (am i : ℤ) = a i := Int.toNat_sub_toNat_neg (a i)
  rw [← hi, congrFun hapam i]; simp

end PrimeResonanceFreeness
end JensenLadder
