import Mathlib

/-!
# Spectral Torelli faithfulness (Tier A)

This file formalizes the geometric core of branch B29
(`spectral-torelli-inverse-problem.md`): the monic **spectral polynomial**
`∏_{ρ∈s}(X − ρ)` faithfully determines the zero multiset `s`.

Equivalently, the elementary-symmetric / coefficient data of the spectral
polynomial are **faithful coordinates** on finite zero configurations — and,
through the Newton identities in characteristic zero (`SecularNewton.lean`,
`MomentReconstruction.lean`), so are the secular power sums `s_m = Σ_ρ ρ^m`
(the "Object-X" secular moments). The inverse map is `Polynomial.roots`.

This is the *injectivity* (faithfulness) half of B29. It says nothing about the
*image* (which multisets are genuine zero sets — the three-cut (E)/(A)/(P)
characterization), nor about RH, DSS, or the period realization.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- **B29 (spectral Torelli, geometric core).** The monic spectral polynomial
`∏_{ρ∈s}(X − ρ)` faithfully determines the zero multiset `s`: equal spectral
polynomials force equal multisets. The inverse is `Polynomial.roots`
(`roots_multiset_prod_X_sub_C`). Combined with the Newton bijection in
characteristic zero, the secular moments are faithful coordinates. -/
theorem spectralTorelli_faithful (s t : Multiset ℂ)
    (h : (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod) :
    s = t :=
  calc s = (s.map (fun a => X - C a)).prod.roots :=
        (roots_multiset_prod_X_sub_C s).symm
    _ = (t.map (fun a => X - C a)).prod.roots := by rw [h]
    _ = t := roots_multiset_prod_X_sub_C t

/-- **Vieta product of zeros (B29 ↔ B7 bridge).** The constant term of the
spectral polynomial `∏_{ρ∈s}(X − ρ)` is `(−1)^{#s} · ∏_{ρ∈s} ρ`: the product of
the zeros (up to sign) is a single coefficient. This is the secular datum that
the Arakelov product formula `∏_ρ w_ρ = 1` (B7) constrains. -/
theorem spectralPoly_coeff_zero (s : Multiset ℂ) :
    ((s.map (fun a => X - C a)).prod).coeff 0
      = (-1) ^ (Multiset.card s) * s.prod := by
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub]
  exact Multiset.prod_map_neg s

/-- **Self-dual reality at the coefficient level.** If a Satake/zero multiset `s`
is conjugation-invariant (the self-duality `π ≅ π̄`), then the spectral polynomial
`∏_{a∈s}(X − a)` has **real coefficients** (each fixed by conjugation) — the
reality of the Dirichlet/L-coefficients of a self-dual representation, the
coefficient-level companion of `SatakeReality.selfDual_moment_real`. -/
theorem selfDual_spectralPoly_coeff_real (s : Multiset ℂ)
    (hs : s.map (fun a => (starRingEnd ℂ) a) = s) (k : ℕ) :
    (starRingEnd ℂ) (((s.map (fun a => X - C a)).prod).coeff k)
      = ((s.map (fun a => X - C a)).prod).coeff k := by
  have hP : Polynomial.map (starRingEnd ℂ) ((s.map (fun a => X - C a)).prod)
      = (s.map (fun a => X - C a)).prod := by
    rw [Polynomial.map_multiset_prod, Multiset.map_map,
      show (Polynomial.map (starRingEnd ℂ) ∘ fun a : ℂ => X - C a)
          = ((fun a : ℂ => X - C a) ∘ (fun a : ℂ => (starRingEnd ℂ) a)) from by
        funext a; simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C],
      ← Multiset.map_map (fun a : ℂ => X - C a) (fun a : ℂ => (starRingEnd ℂ) a), hs]
  conv_rhs => rw [← hP]
  rw [Polynomial.coeff_map]

end

end GaloisForLFunctions
