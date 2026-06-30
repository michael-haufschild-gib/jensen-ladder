import GaloisForLFunctions.CompleteHomogeneous
import GaloisForLFunctions.ExteriorSatake

/-!
# The `e–h` (∧•/Sym•) Koszul duality — welding B30 to B5 (Tier A)

This file proves the **`e–h` duality** `Σ_{i+j=k} (−1)ⁱ eᵢ hⱼ = δ_{k,0}` for the
Satake parameters of a `GLₙ` family `f : Fin n → ℂ`, where `eᵢ` is the elementary
symmetric function (`∧ⁱ`, the local-`L`-factor coefficient, `ExteriorSatake.lean`)
and `hⱼ` is the complete homogeneous symmetric function (`Symʲ`, the
`MvPolynomial.hsymm` character, `CompleteHomogeneous.lean`).

This is the **Koszul-exactness identity** `∧• ⊣ Sym•` that welds branch B30
(`spectral-functoriality-operations-calculus.md §9`, the operations λ-ring) to
branch B5 (`difference-galois-cohomology.md §6`, the cohomology grading): the
generating series `E(X) = ∏(1 − fᵢX) = Σ(−1)ᵏeₖXᵏ` and
`H(X) = ∏(1 − fᵢX)⁻¹ = ΣhₖXᵏ` are mutually reciprocal (`E·H = 1`), and the
`e–h` duality is the coefficient form of that reciprocity. It closes the
degree-`≥ 2` extension of the degree-1 base case
`CompleteHomogeneous.symChar_one_eq_esymm_one`.

mathlib has the `e–p` Newton identity but **not** the `e–h` duality nor the
complete-homogeneous generating function, so this builds the reciprocity from
scratch: the geometric series `(1 − rX)·ΣrᵐXᵐ = 1` in `ℂ⟦X⟧`
(`geometric_localFactor_inv`), the local-factor coefficient
(`coeff_localFactor_series`), and the complete-homogeneous generating function
`coeff_k ∏(1 − fᵢX)⁻¹ = hₖ` (`coeff_completeHomogeneous_series`, via the
`Sym ↔ Finsupp` multiplicity bijection).

This is the finite/multiplicative (Satake-side) shadow of the B5 Koszul complex;
it does **not** formalize the infinite-prime limit (the `ω ∈ H²` monoidality
obstruction = Koszul homology in the `∏_p` limit), which stays in the drafts.
-/

open PowerSeries
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {n : ℕ}

/-- **Geometric series for one local factor.** In `ℂ⟦X⟧`, the local factor
`1 − rX` is inverted by the geometric series `Σ_m rᵐ Xᵐ`: `(1 − rX)·(Σ rᵐXᵐ) = 1`.
This is the per-prime reciprocity underlying the `e–h` duality. -/
theorem geometric_localFactor_inv (r : ℂ) :
    (1 - PowerSeries.C r * X) * (mk fun m => r ^ m) = 1 := by
  have key : (1 - PowerSeries.C r * X) * (mk fun m => r ^ m)
           = (mk fun m => r ^ m) - PowerSeries.C r * (X * (mk fun m => r ^ m)) := by ring
  rw [key]; ext m
  simp only [map_sub, coeff_C_mul]
  rcases m with _ | m
  · simp [coeff_mk, coeff_zero_X_mul, coeff_one]
  · rw [coeff_mk, coeff_succ_X_mul, coeff_mk, coeff_one]
    simp only [Nat.succ_ne_zero, if_false, pow_succ]; ring

/-- **The `∧•` generating series (local `L`-factor).** The coefficient of `Xᵏ` in
`E(X) = ∏ᵢ (1 − fᵢX)` is the signed elementary symmetric function
`(−1)ᵏ eₖ(f)` — the exterior-power (`∧ᵏ`) Satake datum. The power-series form of
`ExteriorSatake.localFactor_coeff_esymm`, obtained via the polynomial coercion. -/
theorem coeff_localFactor_series (f : Fin n → ℂ) (k : ℕ) :
    (PowerSeries.coeff k) (∏ i, (1 - PowerSeries.C (f i) * PowerSeries.X))
      = (-1) ^ k * (Finset.univ.val.map f).esymm k := by
  have hcoe : ((∏ i, (1 - Polynomial.C (f i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ)
            = ∏ i, (1 - PowerSeries.C (f i) * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Polynomial.coeToPowerSeries.ringHom_apply]
    push_cast [Polynomial.coe_C, Polynomial.coe_X]; ring
  rw [← hcoe, Polynomial.coeff_coe]
  have hmul : (∏ i, (1 - Polynomial.C (f i) * Polynomial.X) : Polynomial ℂ)
            = ((Finset.univ.val.map f).map (fun a => 1 - Polynomial.C a * Polynomial.X)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hmul, localFactor_coeff_esymm]

/-- **The `Sym•` generating series (complete homogeneous).** The coefficient of
`Xᵏ` in `H(X) = ∏ᵢ (1 − fᵢX)⁻¹ = ∏ᵢ (Σ_m fᵢᵐ Xᵐ)` is the complete homogeneous
symmetric function `hₖ(f) = aeval f (hsymm k)` — the `Symᵏ` Satake character. This
is the complete-homogeneous generating function (a mathlib gap), proved via the
`Sym (Fin n) k ↔ {Finsupp summing to k}` multiplicity bijection between the
`hsymm` monomials and the Cauchy-product (`coeff_prod`) terms. -/
theorem coeff_completeHomogeneous_series (f : Fin n → ℂ) (k : ℕ) :
    (PowerSeries.coeff k) (∏ i, (mk fun m => (f i) ^ m))
      = (MvPolynomial.aeval f) (MvPolynomial.hsymm (Fin n) ℂ k) := by
  rw [PowerSeries.coeff_prod, aeval_hsymm_eq]
  simp only [coeff_mk]
  symm
  apply Finset.sum_bij'
    (i := fun (s : Sym (Fin n) k) _ => Multiset.toFinsupp s.1)
    (j := fun (l : Fin n →₀ ℕ) hl => (⟨Finsupp.toMultiset l, by
        rw [Finsupp.card_toMultiset, Finsupp.sum_fintype l (fun _ => id) (fun _ => rfl)]
        exact (Finset.mem_finsuppAntidiag.mp hl).1⟩ : Sym (Fin n) k))
  case hi =>
    intro s _
    refine Finset.mem_finsuppAntidiag.mpr ⟨?_, Finset.subset_univ _⟩
    have h1 : (Multiset.toFinsupp s.1).sum (fun _ => id) = k := by
      rw [Multiset.toFinsupp_sum_eq]; exact s.2
    rw [Finsupp.sum_fintype (Multiset.toFinsupp s.1) (fun _ => id) (fun _ => rfl)] at h1
    exact h1
  case hj => intro l _; exact Finset.mem_univ _
  case left_neg =>
    intro s _; apply Subtype.ext; exact Multiset.toFinsupp_toMultiset s.1
  case right_neg => intro l _; exact Finsupp.toMultiset_toFinsupp l
  case h =>
    intro s _
    rw [Finset.prod_multiset_map_count]
    simp only [Multiset.toFinsupp_apply]
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro i _ hi
    rw [Multiset.count_eq_zero.mpr (by simpa using hi), pow_zero]

/-- **The `e–h` (`∧•`/`Sym•`) Koszul duality.** For `k ≥ 1`,
`Σ_{i+j=k} (−1)ⁱ eᵢ(f) hⱼ(f) = 0`, the Koszul-exactness identity welding the
elementary-symmetric (`∧ⁱ`, B30) and complete-homogeneous (`Symʲ`, B30) bases —
the finite Satake-side shadow of the B5 Koszul complex
(`difference-galois-cohomology.md §6`). Read off the reciprocity `E·H = 1` of the
two generating series via the Cauchy product: the `k`-th coefficient of `1`
vanishes for `k ≥ 1`. Extends the degree-1 base case
`CompleteHomogeneous.symChar_one_eq_esymm_one` to all degrees. -/
theorem eh_koszul_duality (f : Fin n → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ Finset.antidiagonal k,
      (-1) ^ (p.1) * (Finset.univ.val.map f).esymm p.1
        * (MvPolynomial.aeval f) (MvPolynomial.hsymm (Fin n) ℂ p.2) = 0 := by
  have hEH : (∏ i, (1 - PowerSeries.C (f i) * PowerSeries.X))
             * (∏ i, (mk fun m => (f i) ^ m)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => geometric_localFactor_inv (f i))
  have hcoeff := congrArg (PowerSeries.coeff k) hEH
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, if_neg (by omega)] at hcoeff
  rw [← hcoeff]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [coeff_localFactor_series, coeff_completeHomogeneous_series, mul_assoc]

end

end GaloisForLFunctions
