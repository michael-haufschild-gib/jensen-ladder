import Mathlib

/-!
# Newton's identities for multisets — the inversion engine for B29 (Tier A)

This file builds the Newton-identity infrastructure for branch B29
(`spectral-torelli-inverse-problem.md`): the secular-moment Torelli problem asks
whether the secular **power sums** `p_k = Σ_ρ ρ^k` faithfully determine the zero
multiset. The polynomial/elementary-symmetric half is already ledger-proven
(`SpectralTorelli.spectralTorelli_faithful`, `spectralPoly_coeff_zero`); the
missing engine is **Newton's identity for a multiset**, which (in characteristic
zero) inverts the power sums to recover the elementary symmetric functions `e_k`,
hence the spectral polynomial, hence the multiset.

mathlib provides Newton's identities only for `MvPolynomial`
(`MvPolynomial.psum_eq_mul_esymm_sub_sum`) and the esymm bridge
`aeval_esymm_eq_multiset_esymm`. Here we add the missing **psum bridge** and
transfer Newton's identity to multisets via `aeval`.

This is the Tier-A symmetric-function infrastructure; the characteristic-zero
inversion and the final faithfulness conclusion are the next steps of the B29
build (not in this file yet).
-/

open scoped BigOperators
open MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Power-sum bridge.** `aeval f` sends the `MvPolynomial` power sum `psum σ R k`
to the multiset power sum `Σ_i f(i)^k`. This is the companion of mathlib's
`MvPolynomial.aeval_esymm_eq_multiset_esymm`, which mathlib does not provide. -/
theorem aeval_psum_eq_multiset_powerSum {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype σ] [Algebra R S] (k : ℕ) (f : σ → S) :
    (aeval f) (MvPolynomial.psum σ R k) = (Finset.univ.val.map (fun i => f i ^ k)).sum := by
  rw [MvPolynomial.psum, map_sum]
  simp_rw [map_pow, aeval_X]
  rfl

/-- **Newton's identity for a multiset** (the B29 inversion engine). For a finite
family `f : Fin n → S` over a commutative ring, the multiset power sum `p_k`, the
elementary symmetric function `e_k`, and the lower power sums/esymm satisfy
Newton's recursion
`p_k = (-1)^{k+1} · k · e_k − Σ_{0<a<k} (-1)^a · e_a · p_{k-a}`.
Transferred from `MvPolynomial.psum_eq_mul_esymm_sub_sum` via the esymm/psum
`aeval` bridges. In characteristic zero (`k` invertible) this **solves for `e_k`**
in terms of `p_1,…,p_k` and `e_0,…,e_{k-1}` — the recursion that recovers the
spectral polynomial, hence the zero multiset, from the secular power sums. -/
theorem multiset_newton {S : Type*} [CommRing S] {n : ℕ} (f : Fin n → S) (k : ℕ) (hk : 0 < k) :
    (Finset.univ.val.map (fun i => f i ^ k)).sum
      = (-1) ^ (k + 1) * k * (Finset.univ.val.map f).esymm k
        - ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
            (-1) ^ a.1 * (Finset.univ.val.map f).esymm a.1
              * (Finset.univ.val.map (fun i => f i ^ a.2)).sum := by
  have key := congrArg (aeval f) (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) S k hk)
  rw [aeval_psum_eq_multiset_powerSum] at key
  rw [key, map_sub, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    aeval_esymm_eq_multiset_esymm, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, map_mul, map_pow, map_neg, map_one, aeval_esymm_eq_multiset_esymm,
    aeval_psum_eq_multiset_powerSum]

end

end GaloisForLFunctions
