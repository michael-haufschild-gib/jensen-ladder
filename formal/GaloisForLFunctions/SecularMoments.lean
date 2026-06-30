import GaloisForLFunctions.Core

/-!
# The Object-X pointwise identity: Li's criterion ⟷ secular moments (Tier A)

`hypertranscendental_galois_field_foundations.md` §20 / `dss-multiplicity-estimate-spectral-genericity.md`:
the field's **Object-X** is the secular-moment sequence `P_k = Σ_ρ ρ^{-k}` (power sums over the
nontrivial zeros). It carries **two faces of one point**:

* the **RH face** — Li's criterion `λ_n = Σ_ρ [1 - (1 - 1/ρ)^n] ≥ 0 ∀n`;
* the **DSS face** — algebraic genericity of `{P_k}` (transcendence of the spectrum).

These are linked by the **unipotent-triangular** change of basis
`λ_n = Σ_{j=1}^{n} C(n,j) (-1)^{j+1} P_j`. The *analytic* statement (the sums over the infinitely
many zeros) is Tier C and stays in the drafts. Its **pure-algebra pointwise skeleton** — the per-zero
identity, with `x = 1/ρ` — is Tier A and is what makes the change of basis triangular over `ℤ`:

  `1 - (1 - x)^n = Σ_{j=1}^{n} C(n,j) (-1)^{j+1} x^j`   (reindexed `j ↦ j+1` over `range n`).

Summing this over the zeros (linearity) is exactly `λ_n = Σ_j C(n,j)(-1)^{j+1} P_j`; this file
formalizes only the elementary ring identity, valid in any commutative ring. No zero is summed, no
positivity (RH) and no genericity (DSS) is claimed — both remain frontier.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **The Li ⟷ secular-moment pointwise identity** (the `ℤ`-triangular change of basis, per zero).
With `x = 1/ρ`, the Li summand `1 - (1 - x)^n` equals `Σ_{j=1}^{n} C(n,j) (-1)^{j+1} x^j`
(here reindexed `j ↦ j+1` over `Finset.range n`). Summed over the nontrivial zeros this is
`λ_n = Σ_j C(n,j)(-1)^{j+1} P_j`, linking the RH face (Li positivity) to the DSS face
(secular moments `P_k = Σ_ρ ρ^{-k}`). Pure commutative-ring algebra. -/
theorem li_secular_pointwise (R : Type*) [CommRing R] (x : R) (n : ℕ) :
    1 - (1 - x) ^ n
      = ∑ j ∈ Finset.range n, (n.choose (j + 1) : R) * (-1) ^ j * x ^ (j + 1) := by
  have hbin : (1 - x) ^ n = ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * (-1) ^ i * x ^ i := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun i _ => by rw [neg_pow, one_pow, mul_one]; ring
  rw [hbin, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  rw [add_comm, ← sub_sub, sub_self, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **The inverse Li ⟷ secular-moment identity** (the change of basis the other way, per zero).
`x^k = Σ_{n=1}^{k} C(k,n) (-1)^{n+1} (1 - (1-x)^n)` (reindexed `n ↦ m+1` over `range k`, `k ≥ 1`).
Summed over the zeros this recovers `P_k` from the `λ_n`; together with `li_secular_pointwise` it
shows the two transforms are mutual inverses, so `{P_k}` and `{λ_n}` generate the **same `ℤ`-lattice**
(the RH-coordinates and DSS-coordinates of Object-X coincide). Pure commutative-ring algebra. -/
theorem secular_li_pointwise_inv (R : Type*) [CommRing R] (x : R) (k : ℕ) (hk : 0 < k) :
    x ^ k = ∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) * (1 - (1 - x) ^ (m + 1)) := by
  classical
  have hsplit : (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) * (1 - (1 - x) ^ (m + 1)))
      = (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R))
        - (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) * (1 - x) ^ (m + 1)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun m _ => by ring
  have key : (∑ i ∈ Finset.range (k + 1), (-1) ^ i * (k.choose i : R)) = 0 := by
    rw [show (0 : R) = ((-1 : R) + 1) ^ k from by
          rw [neg_add_cancel]; exact (zero_pow hk.ne').symm, add_pow]
    exact Finset.sum_congr rfl fun i _ => by rw [one_pow]; ring
  rw [Finset.sum_range_succ'] at key
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at key
  have hA : (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R)) = 1 := by
    have hS : (∑ m ∈ Finset.range k, (-1) ^ (m + 1) * (k.choose (m + 1) : R)) = -1 :=
      eq_neg_of_add_eq_zero_left key
    calc (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R))
        = -(∑ m ∈ Finset.range k, (-1) ^ (m + 1) * (k.choose (m + 1) : R)) := by
            rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun m _ => by ring
      _ = -(-1) := by rw [hS]
      _ = 1 := by ring
  have hxk : x ^ k = ∑ i ∈ Finset.range (k + 1), (-1) ^ i * (1 - x) ^ i * (k.choose i : R) := by
    have h0 : ((-(1 - x)) + 1) ^ k = x ^ k := by ring_nf
    rw [add_pow] at h0
    rw [← h0]; exact Finset.sum_congr rfl fun i _ => by rw [one_pow, neg_pow]; ring
  rw [Finset.sum_range_succ'] at hxk
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at hxk
  have hB : (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) * (1 - x) ^ (m + 1))
      = 1 - x ^ k := by
    have hT : (∑ m ∈ Finset.range k, (-1) ^ (m + 1) * (1 - x) ^ (m + 1) * (k.choose (m + 1) : R))
        = x ^ k - 1 := by rw [hxk]; ring
    calc (∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) * (1 - x) ^ (m + 1))
        = -(∑ m ∈ Finset.range k, (-1) ^ (m + 1) * (1 - x) ^ (m + 1) * (k.choose (m + 1) : R)) := by
            rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun m _ => by ring
      _ = -(x ^ k - 1) := by rw [hT]
      _ = 1 - x ^ k := by ring
  rw [hsplit, hA, hB]; ring

/-- **The secular moments are real (conjugate-pair Object-X reality).** A conjugate pair `{t, conj t}`
contributes `t⁻ᵏ + (conj t)⁻ᵏ = 2 Re(t⁻ᵏ)` to the moment `P_k`, which is real. Hence `P_k` of a
conjugate-symmetric spectrum (the functional-equation structure) is a **real** period sequence — a
basic structural fact of the Object-X. -/
theorem conj_pair_moment_real (t : ℂ) (k : ℕ) :
    ((t ^ k)⁻¹ + ((star t) ^ k)⁻¹).im = 0 := by
  have hstar : ((star t) ^ k)⁻¹ = star ((t ^ k)⁻¹) := by rw [← star_pow, star_inv₀]
  rw [hstar, Complex.add_im, show star ((t ^ k)⁻¹) = (starRingEnd ℂ) ((t ^ k)⁻¹) from rfl,
      Complex.conj_im]
  ring

end

end GaloisForLFunctions
