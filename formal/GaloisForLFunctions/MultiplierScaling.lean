import Mathlib

/-!
# Per-prime multiplier scaling preserves real-rootedness (Tier A)

This file formalizes the **finite floor** of Attack 5 in
`docs/drafts/speculative-proofs-grand-conjectures.md`. The prime difference
operator `σ_p : x ↦ p^{-1} x` acts on a real polynomial by the substitution
`P(x) ↦ P(c·x)` with `c = p^{-1} ≠ 0` (here `sigmaScale c P := P.comp (C c * X)`).
At the **polynomial** level it preserves real-rootedness — the real roots are
simply rescaled by `1/c` — so every finite-prime truncation `∏_{p≤P} σ_p`
maps real-rooted polynomials to real-rooted polynomials.

This is the multiplicative/finite Tier-A core only. The draft's Pólya–Schur /
Laguerre–Pólya step is needed solely to pass to the *entire-function* limit
(`deg → ∞`, the infinite prime product); that limit is the wall and is **not**
formalized here. Nothing in this file concerns the LP class, the infinite prime
product, or RH.

`Polynomial.Splits` over the field `ℝ` means the polynomial factors into real
linear factors, i.e. is real-rooted.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- The per-prime scaling operator `σ_c` on real polynomials: substitute
`x ↦ c·x`, i.e. `(σ_c P)(x) = P(c·x)`. For `c = p^{-1}` this is the prime
difference operator `σ_p` of the draft acting on the coefficient sequence. -/
def sigmaScale (c : ℝ) (P : ℝ[X]) : ℝ[X] := P.comp (C c * X)

/-- Evaluation of the scaled polynomial: `(σ_c P)(r) = P(c·r)`. -/
@[simp] theorem sigmaScale_eval (c r : ℝ) (P : ℝ[X]) :
    (sigmaScale c P).eval r = P.eval (c * r) := by
  simp [sigmaScale, eval_comp]

/-- Root correspondence (the scalar core): `r` is a root of `σ_c P` iff `c·r` is
a root of `P`. For `c ≠ 0` the real map `r ↦ c·r` is a bijection of `ℝ`, so it
carries the real roots of `σ_c P` bijectively onto the real roots of `P`. -/
theorem sigmaScale_isRoot (c r : ℝ) (P : ℝ[X]) :
    (sigmaScale c P).IsRoot r ↔ P.IsRoot (c * r) := by
  simp [IsRoot, sigmaScale_eval]

/-- **Finite multiplier closure (the Tier-A floor of Attack 5).** If a real
polynomial `P` is real-rooted (`P.Splits`, i.e. it factors into real linear
factors over `ℝ`) and `c ≠ 0`, then the scaled polynomial `σ_c P` is again
real-rooted. The proof is elementary real algebra: each linear factor `X - C a`
becomes `C c · X - C a = C c · (X - C (c⁻¹·a))`, still a real linear factor. -/
theorem sigmaScale_splits (c : ℝ) (hc : c ≠ 0) (P : ℝ[X])
    (hP : P.Splits) : (sigmaScale c P).Splits := by
  -- comp by `C c * X` pushed through a product of linear factors
  have prod_comp : ∀ (m : Multiset ℝ),
      ((Multiset.map (fun x => X - C x) m).prod).comp (C c * X)
        = (Multiset.map (fun a => C c * X - C a) m).prod := by
    intro m
    induction m using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, sub_comp,
          X_comp, C_comp, ih]
  -- a product of scaled linear factors splits (each factor is `C c · (X - C b)`)
  have prod_splits : ∀ (m : Multiset ℝ),
      (Multiset.map (fun a => C c * X - C a) m).prod.Splits := by
    intro m
    induction m using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        rw [Multiset.map_cons, Multiset.prod_cons]
        refine Splits.mul ?_ ih
        have h2 : C c * X - C a = C c * (X - C (c⁻¹ * a)) := by
          rw [mul_sub, ← C_mul, mul_inv_cancel_left₀ hc]
        rw [h2]
        exact Splits.mul (Splits.C _) (Splits.X_sub_C _)
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hP
  have key : sigmaScale c P
      = C P.leadingCoeff * (Multiset.map (fun a => C c * X - C a) m).prod := by
    simp only [sigmaScale]
    nth_rewrite 1 [hm]
    rw [mul_comp, C_comp, prod_comp]
  rw [key]
  exact Splits.mul (Splits.C _) (prod_splits m)

end

end GaloisForLFunctions
