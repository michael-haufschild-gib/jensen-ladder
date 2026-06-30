import Mathlib

/-!
# Stieltjes-log weld: coefficient Cauchy product (Tier A)

This file formalizes the elementary coefficient identity from
`docs/drafts/pipeline/2-fully-proven/stieltjes-log-weld.md`.

In the formal variable `u = s - 1`, write

* `F(u) = Σ (c_j / j!) u^j`,
* `G(u) = (s - 1)ζ(s) = 1 + Σ a_n u^(n+1)`,
* `a_n = (-1)^n γ_n / n!`.

The theorem `stieltjes_pairing_cauchy_j` is the Cauchy-product formula with the
top `j = N` term isolated. The paper's displayed formula is the same identity
after reindexing the remaining sum by `n = N - j - 1`.

No analytic continuation, Stieltjes constants, Dirichlet-polynomial independence,
or transcendence claim is formalized here.
-/

open PowerSeries

namespace GaloisForLFunctions

noncomputable section

/-- The Stieltjes-tail coefficient `a_n = (-1)^n γ_n/n!`. -/
def stieltjesA (γ : ℕ → ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * γ n / (Nat.factorial n : ℂ)

/-- Coefficients of `G(u)=(s-1)ζ(s)=1+Σ a_n u^(n+1)` in the formal variable `u=s-1`. -/
def stieltjesGCoeff (γ : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => stieltjesA γ n

/-- Taylor coefficients of the auxiliary `F`, normalized so coefficient `j` is `c_j/j!`. -/
def auxiliaryTaylorCoeff (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  c j / (Nat.factorial j : ℂ)

/-- Cauchy product for the Stieltjes pairing with the top auxiliary term isolated.

This is the `j`-indexed form of the card's formula
`[H]_N = c_N/N! + Σ_{n<N} c_{N-n-1}/(N-n-1)! * (-1)^n γ_n/n!`. -/
theorem stieltjes_pairing_cauchy_j (c γ : ℕ → ℂ) (N : ℕ) :
    (PowerSeries.coeff N)
      ((PowerSeries.mk (auxiliaryTaylorCoeff c)) * (PowerSeries.mk (stieltjesGCoeff γ))) =
      auxiliaryTaylorCoeff c N +
        ∑ j ∈ Finset.range N,
          auxiliaryTaylorCoeff c j * stieltjesA γ (N - j - 1) := by
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => auxiliaryTaylorCoeff c j * stieltjesGCoeff γ k) N]
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ x ∈ Finset.range N,
          auxiliaryTaylorCoeff c x * stieltjesGCoeff γ (N - x)) =
        ∑ j ∈ Finset.range N,
          auxiliaryTaylorCoeff c j * stieltjesA γ (N - j - 1) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < N := Finset.mem_range.mp hj
    have hsucc : N - j = (N - j - 1) + 1 := by omega
    rw [hsucc]
    simp [stieltjesGCoeff]
  have htop : auxiliaryTaylorCoeff c N * stieltjesGCoeff γ (N - N) = auxiliaryTaylorCoeff c N := by
    simp [stieltjesGCoeff]
  rw [hsum, htop, add_comm]

end

end GaloisForLFunctions
