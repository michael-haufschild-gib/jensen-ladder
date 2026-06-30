import Mathlib

/-!
# Complete-homogeneous (Symᵏ) Satake character — the third λ-ring basis (Tier A)

This file adds the **`Symᵏ` / complete-homogeneous (`hₖ`)** face of the B30
operations λ-ring (`spectral-functoriality-operations-calculus.md`), the third
standard basis alongside the elementary-symmetric (`∧ᵏ`, `ExteriorSatake.lean`)
and power-sum (`ψᵐ`, `AdamsOperations.lean`) faces. For a Satake family
`f : Fin n → ℂ`, the `Symᵏπ` character is `aeval f (hsymm k) = Σ_{Sym} ∏`, the
complete homogeneous symmetric function of the Satake parameters.

This is the general-`GLₙ` `Symᵏ` (the `GL₂` case being the Chebyshev plethysm of
`SymPowerPlethysm.lean`). It bridges mathlib's `MvPolynomial.hsymm` to the Satake
family via `aeval`, and records the base degrees `Sym⁰ = 1` and `Sym¹ = trace`.
-/

open scoped BigOperators
open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

variable {n : ℕ}

/-- **Symᵏ character as a complete homogeneous symmetric function.** The `Symᵏπ`
character of a Satake family `f` is `Σ_{s : Sym (Fin n) k} ∏ f(s)`, the complete
homogeneous symmetric function of the Satake parameters (bridging mathlib's
`MvPolynomial.hsymm` to the family via `aeval`). -/
theorem aeval_hsymm_eq (f : Fin n → ℂ) (k : ℕ) :
    (aeval f) (MvPolynomial.hsymm (Fin n) ℂ k) = ∑ s : Sym (Fin n) k, (s.1.map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  congr 1
  ext s
  rw [map_multiset_prod, Multiset.map_map]
  simp

/-- **Sym⁰ = 1** (the trivial representation). -/
theorem symChar_zero (f : Fin n → ℂ) :
    (aeval f) (MvPolynomial.hsymm (Fin n) ℂ 0) = 1 := by
  rw [MvPolynomial.hsymm_zero, map_one]

/-- **Sym¹ character = the trace `p₁ = Σ αᵢ`** (the standard representation). At
degree one all three λ-ring bases coincide: `Sym¹ = ∧¹ = ψ¹ = p₁`. -/
theorem symChar_one (f : Fin n → ℂ) :
    (aeval f) (MvPolynomial.hsymm (Fin n) ℂ 1) = ∑ i, f i := by
  rw [MvPolynomial.hsymm_one, map_sum]
  simp [aeval_X]

/-- **Symᵏ temperedness (Ramanujan bound for the complete homogeneous).** For a
unitary Satake family (all `‖f i‖ ≤ 1`), the `Symᵏπ` character is bounded by the
dimension of `Symᵏ`: `‖hₖ‖ ≤ |Sym (Fin n) k|` (`= binom(n+k-1, k)`). Each of the
`|Sym|` complete-homogeneous monomials is a product of norm-`≤1` Satake
parameters, so the triangle inequality gives the bound. Together with
`ExteriorSatake.esymm_norm_le` (`∧ᵏ`) and `ExteriorSatake.multiset_powerSum_norm_le`
(`ψᵏ`) this bounds **all three** λ-ring bases for tempered Satake data. -/
theorem symChar_norm_le (f : Fin n → ℂ) (hs : ∀ i, ‖f i‖ ≤ 1) (k : ℕ) :
    ‖(aeval f) (MvPolynomial.hsymm (Fin n) ℂ k)‖ ≤ (Fintype.card (Sym (Fin n) k) : ℝ) := by
  have hprod : ∀ m : Multiset (Fin n), ‖(m.map f).prod‖ ≤ 1 := by
    intro m
    induction m using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
        exact mul_le_one₀ (hs a) (norm_nonneg _) ih
  rw [aeval_hsymm_eq]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s : Sym (Fin n) k, ‖(s.1.map f).prod‖
      ≤ ∑ _s : Sym (Fin n) k, (1 : ℝ) := Finset.sum_le_sum (fun s _ => hprod s.1)
    _ = (Fintype.card (Sym (Fin n) k) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **The degree-1 `e–h` (Koszul) duality `h₁ = e₁`.** At degree one the complete
homogeneous character `Sym¹` (`CompleteHomogeneous.symChar_one`) and the elementary
symmetric datum `∧¹ = e₁` (`ExteriorSatake.localFactor_coeff_esymm` at `k=1`)
coincide: `aeval f (hsymm 1) = e₁(α)`, both equal to the trace `Σαᵢ`. This is the
base case (`k=1`) of the `∧•`/`Sym•` (`e–h`) duality `Σ_{i+j=k}(−1)ⁱeᵢhⱼ = δ_{k,0}`,
the Koszul-exactness identity that welds the operations λ-ring (B30) to the
difference-Galois cohomology grading (B5,
`difference-galois-cohomology.md §6`). The higher-degree duality is the next
Tier-A target (it needs the `e–h` generating-series reciprocity, a mathlib gap). -/
theorem symChar_one_eq_esymm_one (f : Fin n → ℂ) :
    (aeval f) (MvPolynomial.hsymm (Fin n) ℂ 1) = (Finset.univ.val.map f).esymm 1 := by
  have hesymm1 : ∀ s : Multiset ℂ, s.esymm 1 = s.sum := by
    intro s
    simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map, Function.comp,
      Multiset.prod_singleton]
  rw [symChar_one, hesymm1]
  rfl

end

end GaloisForLFunctions
