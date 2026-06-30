import Mathlib
import JensenLadder.HermiteHankelDetector

/-!
# Bezoutian = residue-Gram: the bivariate identity (gap-1 of the faithful column)

This file proves the **bivariate Bezoutian identity** that `HermiteHankelDetector.lean`'s
docstrings (the `weighted_gram_posSemidef_iff` / `cofactor_decomposition` block, L138–141 and
L197–199) explicitly name as one of the two *remaining classical pieces* for the full polynomial
Hermite–Biehler statement:

  `A(s)·B(t) − A(t)·B(s) = (s − t) · ∑ⱼ rⱼ · Aⱼ(s) · Aⱼ(t)`,

where `A = ∏ₖ (X − αₖ)` has **distinct** roots `αₖ`, `B` has `degree < n`,
`Aⱼ = ∏_{k≠j} (X − αₖ)` is the `j`-th cofactor, and `rⱼ = B(αⱼ)/∏_{k≠j}(αⱼ−αₖ) = B(αⱼ)/A'(αⱼ)`
is the partial-fraction residue of `B/A` at `αⱼ`.

Dividing by `(s − t)` this says the Bezoutian kernel of `(A,B)` equals the residue-weighted
cofactor Gram `∑ⱼ rⱼ Aⱼ(s)Aⱼ(t)`; extracting the `sⁱtᵏ` coefficient gives the matrix identity
`Bez(A,B) = ∑ⱼ rⱼ · (coeffs Aⱼ)(coeffs Aⱼ)ᵀ`, which feeds `weighted_gram_posSemidef_iff`
(`Bez ⪰ 0 ⟺ all residues ≥ 0`) — the faithful, signed read-off of the off-circle index `κ₋`.

The proof is the one-line **brick** `A(s)Aⱼ(t) − A(t)Aⱼ(s) = (s−t)Aⱼ(s)Aⱼ(t)` (from
`A = (X−αⱼ)·Aⱼ`) summed against the already-proven `HermiteHankelDetector.cofactor_decomposition`
(`B = ∑ⱼ rⱼ Aⱼ`). Numerically pre-certified at dps=50 in
`scripts/research/hilbertPolya/theorist_bezoutian_residue_v1.py`. RH-free, axiom-clean.
-/

open Polynomial Finset

namespace JensenLadder
namespace BezoutianResidue

variable {n : ℕ} (α : Fin n → ℝ)

/-- Evaluation of a finite product `∏_{k∈s} (X − αₖ)` is the real product `∏_{k∈s} (x − αₖ)`. -/
theorem eval_prod_sub (s : Finset (Fin n)) (x : ℝ) :
    (∏ k ∈ s, (Polynomial.X - Polynomial.C (α k))).eval x = ∏ k ∈ s, (x - α k) := by
  rw [Polynomial.eval_prod]
  exact Finset.prod_congr rfl
    (fun k _ => by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])

/-- **The brick.** Since `A = ∏ₖ(X−αₖ) = (X−αⱼ)·Aⱼ`, evaluating at `s,t` gives
`(∏ₖ(s−αₖ))·Aⱼ(t) − (∏ₖ(t−αₖ))·Aⱼ(s) = (s−t)·Aⱼ(s)·Aⱼ(t)`. -/
theorem bezout_brick (j : Fin n) (s t : ℝ) :
    (∏ k, (s - α k)) * (∏ k ∈ univ.erase j, (t - α k))
      - (∏ k, (t - α k)) * (∏ k ∈ univ.erase j, (s - α k))
      = (s - t) * ((∏ k ∈ univ.erase j, (s - α k)) * (∏ k ∈ univ.erase j, (t - α k))) := by
  have hs : (∏ k, (s - α k)) = (s - α j) * ∏ k ∈ univ.erase j, (s - α k) :=
    (Finset.mul_prod_erase univ (fun k => s - α k) (Finset.mem_univ j)).symm
  have ht : (∏ k, (t - α k)) = (t - α j) * ∏ k ∈ univ.erase j, (t - α k) :=
    (Finset.mul_prod_erase univ (fun k => t - α k) (Finset.mem_univ j)).symm
  rw [hs, ht]; ring

/-- **The bivariate Bezoutian = residue-Gram identity.** For `A = ∏ₖ(X−αₖ)` with distinct roots
and `B` of `degree < n`, with residues `rⱼ = B(αⱼ)/∏_{k≠j}(αⱼ−αₖ)`:
`A(s)·B(t) − A(t)·B(s) = (s−t)·∑ⱼ rⱼ·Aⱼ(s)·Aⱼ(t)`. -/
theorem bezout_eq_residue_gram (B : Polynomial ℝ)
    (hα : Function.Injective α) (hB : B.degree < (n : ℕ)) (s t : ℝ) :
    (∏ k, (s - α k)) * B.eval t - (∏ k, (t - α k)) * B.eval s
      = (s - t) * ∑ j, (B.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k))
            * ((∏ k ∈ univ.erase j, (s - α k)) * (∏ k ∈ univ.erase j, (t - α k))) := by
  -- `B(x) = ∑ⱼ rⱼ · Aⱼ(x)` at any real `x`, from the in-tree cofactor decomposition.
  have hBeval : ∀ x : ℝ, B.eval x
      = ∑ j, (B.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k)) * ∏ k ∈ univ.erase j, (x - α k) := by
    intro x
    conv_lhs => rw [HermiteHankelDetector.cofactor_decomposition α B hα hB]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_smul, smul_eq_mul, eval_prod_sub]
  rw [hBeval s, hBeval t, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hbrick := bezout_brick α j s t
  linear_combination (B.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k)) * hbrick

end BezoutianResidue
end JensenLadder
