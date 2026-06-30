import GaloisForLFunctions.EHKoszulDuality
import GaloisForLFunctions.SymPowerPlethysm

/-!
# The `GL₂` symmetric-power character = Chebyshev `S` (Sato–Tate skeleton, Tier A)

This file formalizes the algebraic heart of the Sato–Tate dictionary of the
automorphic continent (`automorphic-continent-rankin-selberg-ramanujan.md` §3′):
for a `GL₂` Satake parameter pair `(z, z⁻¹)`, the **symmetric-power character**
`Symᵏ` is the Chebyshev polynomial `S_k` evaluated at the trace `z + z⁻¹`:

  `χ_{Symᵏ}(z, z⁻¹) = aeval ![z, z⁻¹] (hsymm (Fin 2) ℂ k) = S_k(z + z⁻¹)`.

Equivalently, with `z = e^{iθ}` and `a_p = z + z⁻¹ = 2cos θ`, this is
`Symᵏ a_p = U_k(cos θ_p)` — the identity whose equidistribution (against the
Sato–Tate measure `(2/π)sin²θ dθ`, against which the `U_k` are orthonormal) **is**
Sato–Tate. It welds the complete-homogeneous (`Symᵏ`) character of
`CompleteHomogeneous.lean`/`EHKoszulDuality.lean` to the Chebyshev–Laurent
plethysm of `SymPowerPlethysm.lean` via the generating function
`coeff_completeHomogeneous_series`.

We also record the `GL₂` temperedness/Ramanujan bound `‖Symᵏ‖ ≤ k+1` for a
unitary Satake parameter (`‖z‖ = 1`), with the dimension count
`|Sym (Fin 2) k| = k+1`.

This is the prime/Satake-side character identity and the finite tempered bound
only. It is **not** the Sato–Tate equidistribution theorem, the Sato–Tate measure,
the orthogonality of the `U_k`, or Ramanujan for automorphic forms.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **`GL₂` symmetric-power character is Chebyshev `S` of the trace.** For a
nonzero `GL₂` Satake parameter `z` (with contragredient `z⁻¹`), the `Symᵏ`
character `aeval ![z, z⁻¹] (hsymm (Fin 2) ℂ k)` equals `S_k(z + z⁻¹)`, the
Chebyshev polynomial of the trace. With `z = e^{iθ}`, `z + z⁻¹ = 2cos θ`, this is
`Symᵏ a_p = U_k(cos θ_p)` — the Sato–Tate symmetric-power character identity.
Proved by clearing `zᵏ` and matching the complete-homogeneous generating function
(`coeff_completeHomogeneous_series`) to the Chebyshev–Laurent geometric series
(`chebyshevS_eval_add_inv`). -/
theorem symPowerGL2_eq_chebyshevS (z : ℂ) (hz : z ≠ 0) (k : ℕ) :
    (MvPolynomial.aeval ![z, z⁻¹]) (MvPolynomial.hsymm (Fin 2) ℂ k)
      = (Polynomial.Chebyshev.S ℂ (k : ℤ)).eval (z + z⁻¹) := by
  rw [← coeff_completeHomogeneous_series, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  apply mul_left_cancel₀ (pow_ne_zero k hz)
  rw [chebyshevS_eval_add_inv z hz k, Finset.mul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => z ^ k * (z ^ a * (z⁻¹) ^ b))]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [show z ^ k = z ^ a * z ^ (k - a) from by rw [← pow_add, Nat.add_sub_cancel' hak]]
  rw [show z ^ a * z ^ (k - a) * (z ^ a * (z⁻¹) ^ (k - a))
        = (z ^ a * z ^ a) * (z ^ (k - a) * (z⁻¹) ^ (k - a)) from by ring]
  rw [← mul_pow z z⁻¹ (k - a), mul_inv_cancel₀ hz, one_pow, mul_one, ← pow_add, ← two_mul, pow_mul]

/-- **Dimension of the `GL₂` symmetric power.** `|Sym (Fin 2) k| = k + 1`: the
`Symᵏ` of the standard `GL₂` representation has dimension `k+1` (the number of
size-`k` multisets over two letters, `multichoose 2 k`). -/
theorem symPowerGL2_card (k : ℕ) : Fintype.card (Sym (Fin 2) k) = k + 1 := by
  rw [Sym.card_sym_eq_multichoose, Fintype.card_fin, Nat.multichoose_eq,
    show 2 + k - 1 = k + 1 from by omega, Nat.choose_succ_self_right]

/-- **`GL₂` symmetric-power temperedness (Ramanujan bound).** For a unitary `GL₂`
Satake parameter (`‖z‖ = 1`, so the parameters `z, z⁻¹` are on the unit circle),
the `Symᵏ` character is bounded by its dimension: `‖Symᵏ‖ ≤ k+1`. This is the
`GL₂` specialization of `CompleteHomogeneous.symChar_norm_le` via
`symPowerGL2_card`; the Satake-side tempered bound supporting Sato–Tate. -/
theorem symPowerGL2_norm_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖(MvPolynomial.aeval ![z, z⁻¹]) (MvPolynomial.hsymm (Fin 2) ℂ k)‖ ≤ (k : ℝ) + 1 := by
  have hb := symChar_norm_le ![z, z⁻¹] ?_ k
  · rw [symPowerGL2_card] at hb; push_cast at hb; exact hb
  · intro i
    fin_cases i
    · simpa using hz.le
    · simp [hz]

end

end GaloisForLFunctions
