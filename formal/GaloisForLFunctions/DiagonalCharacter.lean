import GaloisForLFunctions.Core

/-!
# The Bohr character on the diagonal is a Dirichlet monomial (Tier A)

`dss-multiplicity-estimate-spectral-genericity.md` §0: the Mahler-style auxiliary
`A(z) = Σ_m c_m z^m` on the prime torus `𝕋^∞`, restricted to the diagonal `F(t) = (p^{-it})_p`,
becomes a **Dirichlet polynomial** `Σ_m c_m N_m^{-it}` with `N_m = ∏_p p^{m_p}`. The load-bearing
algebraic step is per-monomial: the diagonal value of the character `∏_p x_p^{m_p}` is the Dirichlet
monomial of `N_m`. This file formalizes exactly that step (and the two `cpow` lemmas it needs).

`diagonal_character_eq_dirichlet`: `N_m^z = ∏_p (p^z)^{m_p}` for the finite prime product
`N_m = primeProduct m`. Taking `z = -i t` gives `(∏_p p^{m_p})^{-it} = ∏_p (p^{-it})^{m_p}` — the
character evaluated on the diagonal flow equals the Dirichlet monomial. This is "auxiliary =
Dirichlet polynomial" at the monomial level; the analytic zero-count of the resulting Dirichlet
polynomial (the multiplicity estimate, DSS draft §1) is Tier C and stays in the draft.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Complex `cpow` distributes over a finite product of nonnegative-real bases. -/
lemma prod_ofReal_cpow {ι : Type*} (s : Finset ι) (g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) (z : ℂ) :
    ((∏ i ∈ s, (g i : ℂ)) ^ z) = ∏ i ∈ s, ((g i : ℂ) ^ z) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a t)
      have hgt : 0 ≤ ∏ i ∈ t, g i := Finset.prod_nonneg fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have iht := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← iht, ← Complex.ofReal_prod,
          Complex.mul_cpow_ofReal_nonneg hga hgt]

/-- For a nonnegative real base, a natural power commutes past a complex `cpow`:
`(p^m)^z = (p^z)^m`. (Proved as the constant-product special case of `prod_ofReal_cpow`, avoiding
the branch hypotheses of `Complex.cpow_mul`.) -/
lemma natpow_cpow_comm (p : ℝ) (hp : 0 ≤ p) (m : ℕ) (z : ℂ) :
    (((p : ℂ)) ^ m) ^ z = (((p : ℂ)) ^ z) ^ m := by
  have hp1 : ((p : ℂ)) ^ m = ∏ _i ∈ Finset.range m, (p : ℂ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hp1, prod_ofReal_cpow (Finset.range m) (fun _ => p) (fun _ _ => hp) z,
      Finset.prod_const, Finset.card_range]

/-- **The Bohr character on the diagonal is a Dirichlet monomial.**
`N_m^z = ∏_p (p^z)^{m_p}` with `N_m = primeProduct m`. With `z = -i t`:
`(∏_p p^{m_p})^{-it} = ∏_p (p^{-it})^{m_p}` — the auxiliary character `∏_p x_p^{m_p}` evaluated on
the prime-torus diagonal `(p^{-it})_p` is the Dirichlet monomial of `N_m`. The algebraic heart of
"auxiliary = Dirichlet polynomial" in the DSS multiplicity engine. -/
theorem diagonal_character_eq_dirichlet (m : Nat.Primes →₀ ℕ) (z : ℂ) :
    ((primeProduct m : ℕ) : ℂ) ^ z = ∏ p ∈ m.support, (((p : ℕ) : ℂ) ^ z) ^ (m p) := by
  have hbase : ((primeProduct m : ℕ) : ℂ)
      = ∏ p ∈ m.support, (((((p : ℕ) : ℝ)) ^ (m p) : ℝ) : ℂ) := by
    unfold primeProduct
    rw [Finsupp.prod]
    push_cast
    rfl
  rw [hbase, prod_ofReal_cpow m.support (fun p => ((p : ℕ) : ℝ) ^ (m p))
        (fun p _ => pow_nonneg (by positivity) _) z]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [show (((((p : ℕ) : ℝ)) ^ (m p) : ℝ) : ℂ) = (((p : ℕ) : ℂ)) ^ (m p) from by push_cast; ring]
  exact natpow_cpow_comm ((p : ℕ) : ℝ) (by positivity) (m p) z

/-- **Auxiliary on the diagonal is a Dirichlet polynomial** (full sum level, DSS engine §0).
A finite character polynomial `A(z) = Σ_i c_i ∏_p x_p^{(M i)_p}` evaluated on the prime-torus
diagonal (`x_p ↦ p^z`, i.e. `x_p = p^{-it}` at `z = -it`) equals the Dirichlet polynomial
`Σ_i c_i N_{M i}^{z}` over the prime products `N_{M i} = primeProduct (M i)`. Linearity over
`diagonal_character_eq_dirichlet`. This is the foundational identity of the multiplicity engine:
the auxiliary, restricted to the diagonal, is a Dirichlet polynomial. -/
theorem auxiliary_diagonal_eq {ι : Type*} (s : Finset ι)
    (M : ι → (Nat.Primes →₀ ℕ)) (c : ι → ℂ) (z : ℂ) :
    (∑ i ∈ s, c i * ∏ p ∈ (M i).support, ((((p : ℕ) : ℂ)) ^ z) ^ ((M i) p))
      = ∑ i ∈ s, c i * (((primeProduct (M i) : ℕ) : ℂ) ^ z) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagonal_character_eq_dirichlet]

end

end GaloisForLFunctions
