import GaloisForLFunctions.Core

/-!
# Moment ↔ spectrum reconstruction: Newton's identities for a finite spectrum (Tier A/B)

`dss-multiplicity-estimate-spectral-genericity.md` / charter B26 / grand conjecture #7 (the realization
problem). The field's Object-X is the secular-moment sequence `P_k = Σ_ρ ρ^{-k}` — the **power sums**
of the inverse zeros. The inverse-spectral direction ("the moments determine the spectrum") is the
algebraic content of Newton's identities: for a finite root family the power sums `p_k` determine the
elementary symmetric functions `e_k` (the coefficients of the monic polynomial whose roots are the
spectrum), and conversely.

This file records the **evaluated Newton recursion** for a finite root family `r : σ → ℂ` (a finite
truncation of the spectrum): the power sums `Σ_i r_i^j` and the elementary symmetric
`(map r univ).esymm k` satisfy the Newton recursion, so each is a polynomial function of the other
(over `ℚ`). This is the finite/algebraic skeleton of the moment problem for the spectrum — determinacy
in the finite case. The infinite spectrum, its convergence, and the realization (Hankel positivity /
genericity) remain Tier C in the drafts.
-/

open scoped BigOperators

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- **Evaluated Newton recursion (moment ↔ spectrum, finite case).** For a finite root family
`r : σ → ℂ` (a finite truncation of a spectrum), the power sums `p_j = Σ_i r_i^j` (the secular
moments) and the elementary symmetric functions `e_k = (map r univ).esymm k` (the monic-polynomial
coefficients of the spectrum) satisfy Newton's identity
`k · e_k = (-1)^{k+1} Σ_{i+j=k, i<k} (-1)^i e_i p_j`. Hence over `ℚ` the moments determine the
elementary symmetric functions (and conversely): the finite moment problem for the spectrum is
determinate. Obtained by evaluating mathlib's `MvPolynomial.mul_esymm_eq_sum` at `r`. -/
theorem secular_moment_newton {σ : Type*} [Fintype σ] (r : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (Multiset.map r Finset.univ.val).esymm k
      = (-1) ^ (k + 1) * ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1) ^ (a.1) * (Multiset.map r Finset.univ.val).esymm a.1 * (∑ i, (r i) ^ (a.2)) := by
  have h := MvPolynomial.mul_esymm_eq_sum σ ℂ k
  have h2 := congrArg (aeval (R := ℂ) r) h
  simpa [map_mul, map_sum, map_pow, aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
         aeval_X, map_natCast] using h2

end

end GaloisForLFunctions
