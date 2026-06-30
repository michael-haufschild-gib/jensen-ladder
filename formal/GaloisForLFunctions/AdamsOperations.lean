import GaloisForLFunctions.SatakeTensor

/-!
# Adams operations on Satake data: ⊗-multiplicativity of prime power sums (Tier A)

This file formalizes the clean (Satake/prime-side) core of branch B30,
`docs/drafts/spectral-functoriality-operations-calculus.md` §8: the prime power
sum / Adams operation `p_m(π) = Σ_i α_{p,i}^m` is **multiplicative** under the
Rankin–Selberg tensor product, `p_m(π₁ ⊗ π₂) = p_m(π₁)·p_m(π₂)` (the pairwise
products `satakeTensorParameters`), and in the self-dual case `π ⊗ π̃`
(contragredient = conjugate Satake) it equals the **second moment**
`p_m·conj(p_m) = ‖p_m(π)‖²` — the pair-correlation weight, so the draft's
"operations = correlations" identification is *exact*, not approximate.

This is the λ-ring structure on the **Satake side only**. The zero-side
realization — the secular moments `s_j = Σ_ρ ρ^{-j}` of `π₁ ⊗ π₂` as a function
of those of `π₁, π₂` — is the explicit-formula / period-comparison wall and is
**not** formalized here. Nothing about RH, DSS, or Langlands functoriality is
formalized; only the elementary finite-sum algebra of the Adams operations.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The `m`-th prime power sum / Adams operation of a finite Satake-parameter
list: `p_m(α) = Σ_i α_i^m`. On the prime side this is the Frobenius-at-`p^m`
trace `Λ_π(p^m)/log p`. -/
def adamsPowerSum {ι : Type*} [Fintype ι] (α : ι → ℂ) (m : ℕ) : ℂ := ∑ i, (α i) ^ m

/-- **B30 §8(a): ⊗-multiplicativity of the Adams operations.** The prime power
sum is multiplicative under the Rankin–Selberg tensor product (pairwise-product
Satake parameters): `p_m(π₁ ⊗ π₂) = p_m(π₁)·p_m(π₂)`. -/
theorem adamsPowerSum_tensor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → ℂ) (β : κ → ℂ) (m : ℕ) :
    adamsPowerSum (satakeTensorParameters α β) m
      = adamsPowerSum α m * adamsPowerSum β m := by
  unfold adamsPowerSum satakeTensorParameters
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp_rw [mul_pow]

/-- The Adams operation of the contragredient (conjugate Satake parameters) is
the complex conjugate of the Adams operation. -/
theorem adamsPowerSum_conj {ι : Type*} [Fintype ι] (α : ι → ℂ) (m : ℕ) :
    adamsPowerSum (fun i => (starRingEnd ℂ) (α i)) m
      = (starRingEnd ℂ) (adamsPowerSum α m) := by
  unfold adamsPowerSum
  rw [map_sum]
  simp_rw [map_pow]

/-- **B30 §8(a), self-dual case.** For the Rankin–Selberg square `π ⊗ π̃`
(contragredient = conjugate Satake), the Adams operation is the second moment
`p_m·conj(p_m)`. -/
theorem adamsPowerSum_tensor_selfDual {ι : Type*} [Fintype ι] (α : ι → ℂ) (m : ℕ) :
    adamsPowerSum (satakeTensorParameters α (fun i => (starRingEnd ℂ) (α i))) m
      = adamsPowerSum α m * (starRingEnd ℂ) (adamsPowerSum α m) := by
  rw [adamsPowerSum_tensor, adamsPowerSum_conj]

/-- **B30 §8(a), the second moment is a nonnegative real.** The self-dual
Rankin–Selberg Adams operation equals `‖p_m(π)‖²` (here `Complex.normSq`), the
pair-correlation weight of the zeros (Montgomery): "operation = correlation" is
exact, and the weight is manifestly `≥ 0`. -/
theorem adamsPowerSum_tensor_selfDual_normSq {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (m : ℕ) :
    adamsPowerSum (satakeTensorParameters α (fun i => (starRingEnd ℂ) (α i))) m
      = (Complex.normSq (adamsPowerSum α m) : ℂ) := by
  rw [adamsPowerSum_tensor_selfDual, Complex.mul_conj]

/-- **B30 §8, additive λ-ring structure: ⊕-additivity of the Adams operations.**
The prime power sum is additive under the isobaric direct sum `π₁ ⊞ π₂` (whose
Satake parameters are the disjoint union `Sum.elim α β`):
`p_m(π₁ ⊞ π₂) = p_m(π₁) + p_m(π₂)`. Together with `adamsPowerSum_tensor` this
exhibits the two λ-ring operations on the Adams generators — `⊕` adds, `⊗`
multiplies. -/
theorem adamsPowerSum_isobaricSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → ℂ) (β : κ → ℂ) (m : ℕ) :
    adamsPowerSum (Sum.elim α β) m = adamsPowerSum α m + adamsPowerSum β m := by
  unfold adamsPowerSum
  rw [Fintype.sum_sum_type]
  simp

/-- **B30 §7/§8 (Adams composition `ψᵐ∘ψᵏ = ψᵐᵏ`).** Applying the `k`-th Adams
operation (`α_i ↦ α_iᵏ`, i.e. base change / `p^k`-Frobenius) and then taking the
`m`-th power sum yields the `mk`-th power sum: the Adams operations form a
multiplicative monoid `≅ (ℕ, ×)`. -/
theorem adamsPowerSum_comp {ι : Type*} [Fintype ι] (α : ι → ℂ) (k m : ℕ) :
    adamsPowerSum (fun i => (α i) ^ k) m = adamsPowerSum α (k * m) := by
  unfold adamsPowerSum
  simp_rw [← pow_mul]

/-- **B30 §7/§8 (Adams identity `ψ¹ = id`).** The first Adams operation is the
identity on secular data: `p_m(ψ¹π) = p_m(π)`. -/
theorem adamsPowerSum_one {ι : Type*} [Fintype ι] (α : ι → ℂ) (m : ℕ) :
    adamsPowerSum (fun i => (α i) ^ 1) m = adamsPowerSum α m := by
  rw [adamsPowerSum_comp, one_mul]

/-- **B30 §2 (prime-side Weil positivity is free).** Any explicit-formula pairing
built from the Rankin–Selberg second moments `|p_m(π)|²` with nonnegative test
weights `w m ≥ 0` is manifestly nonnegative on the **Satake side**:
`0 ≤ Σ_m w m · |p_m(π)|²`. By `adamsPowerSum_tensor_selfDual_normSq` the summand
is the `π ⊗ π̃` Adams operation, so this is the positivity of the pair-correlation
pairing — *free* on the prime side. (The wall is whether this transfers to the
zero side; that is the period realization, not formalized here.) -/
theorem adams_secondMoment_weil_nonneg {ι : Type*} [Fintype ι] (α : ι → ℂ)
    (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m) (N : ℕ) :
    0 ≤ ∑ m ∈ Finset.range N, w m * Complex.normSq (adamsPowerSum α m) :=
  Finset.sum_nonneg fun m _ => mul_nonneg (hw m) (Complex.normSq_nonneg _)

/-- **B30 (central character / determinant under ⊗).** The product of all Satake
parameters — the central character / top exterior power `∧^top` (the
"determinant" of `π`) — is multiplicative under Rankin–Selberg in the
determinant-of-Kronecker form `det(π₁⊗π₂)=det(π₁)^{dim π₂}·det(π₂)^{dim π₁}`:
`∏_{i,j} α_i β_j = (∏_i α_i)^{|κ|} · (∏_j β_j)^{|ι|}`. -/
theorem satakeDet_tensor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → ℂ) (β : κ → ℂ) :
    (∏ p : ι × κ, satakeTensorParameters α β p)
      = (∏ i, α i) ^ (Fintype.card κ) * (∏ j, β j) ^ (Fintype.card ι) := by
  unfold satakeTensorParameters
  rw [Fintype.prod_prod_type]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]

end

end GaloisForLFunctions
