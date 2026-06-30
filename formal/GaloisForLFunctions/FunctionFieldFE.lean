import Mathlib

/-!
# The Weil functional equation for the function-field `L`-polynomial (D6, Tier A)

This file formalizes the **algebraic core of the Weil functional equation** for
the function-field continent (`geometric-rosetta-function-field-continent.md`, D6).
For a smooth projective curve `C/F_q`, the zeta function is
`Z(T) = L(T)/((1−T)(1−qT))` with `L(T) = ∏_i (1 − ω_i T)` the numerator, the `ω_i`
the Frobenius eigenvalues. The functional equation is the statement that the
multiset of eigenvalues is **closed under `ω ↦ q/ω`** (the weight-`1` / Poincaré
duality pairing); the Riemann Hypothesis (Deligne/Weil II) is the *further* purity
statement `|ω_i| = √q`, which is **not** formalized here.

The `ω ↦ q/ω` closure alone is a purely algebraic symmetry, and we machine-check
its consequences for the `L`-polynomial:

- `multiset_esymm_map_mul` (mathlib gap-fill): `eₖ(c·S) = cᵏ eₖ(S)` — homogeneity
  of the elementary symmetric function under scaling.
- `functionField_esymm_FE`: the **coefficient-level Weil FE** — closure under
  `ω ↦ q/ω` gives `eₖ(S) = qᵏ · eₖ(S⁻¹)`, the `q`-weighted palindrome of the
  `L`-polynomial coefficients.
- `functionField_localFactor_FE`: the **polynomial-level Weil FE** — the `L`-factor
  `∏(1 − ωT)` is invariant under `ω ↦ q/ω`, i.e. fixed by the FE substitution.

This is the `q`-weighted analog of `LocalFactorDuality.selfDual_localFactor_eq`
(which is the `q = 1` / unitary case `ω ↦ ω⁻¹`). After the purity normalization
`ω = √q · u`, the FE pairing `ω ↦ q/ω` becomes the unitary self-duality `u ↦ u⁻¹`,
so the function-field case reduces to the unitary Satake machinery. This formalizes
the **functional-equation symmetry only** — the purity `|ω|=√q` (RH for curves,
Deligne) and the count `#C(F_q) = q + 1 − Σ ω_i` (Lefschetz) stay imported/Tier C.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Homogeneity of the elementary symmetric function** (mathlib gap-fill).
Scaling every entry of a multiset by `c` scales `eₖ` by `cᵏ`:
`eₖ(c·S) = cᵏ · eₖ(S)` (each `k`-subset product scales by `cᵏ`). -/
theorem multiset_esymm_map_mul (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun a => c * a)).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  simp only [Function.comp_apply]
  rw [show (fun a => c * a) = (fun a : ℂ => (fun _ => c) a * a) from rfl, Multiset.prod_map_mul,
    Multiset.map_const', Multiset.prod_replicate, ht.2, Multiset.map_id']

/-- **The coefficient-level Weil functional equation.** If the Frobenius-eigenvalue
multiset `S` is closed under the duality pairing `ω ↦ q/ω` (`S.map (q/·) = S`), then
the elementary symmetric functions — the coefficients of the `L`-polynomial
`L(T) = ∏(1 − ωT) = Σ (−1)ᵏ eₖ Tᵏ` — satisfy the `q`-weighted relation
`eₖ(S) = qᵏ · eₖ(S⁻¹)`. This is the algebraic form of the Weil FE (no purity / no
RH): `S = S.map (q/·) = (S⁻¹).map (q·)`, and `eₖ` scales by `qᵏ`. -/
theorem functionField_esymm_FE (q : ℂ) (S : Multiset ℂ)
    (hclosed : S.map (fun ω => q / ω) = S) (k : ℕ) :
    S.esymm k = q ^ k * (S.map (fun ω => ω⁻¹)).esymm k := by
  have hmap : S.map (fun ω => q / ω) = (S.map (fun ω => ω⁻¹)).map (fun a => q * a) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro ω _
    rw [Function.comp_apply, div_eq_mul_inv]
  conv_lhs => rw [← hclosed, hmap]
  rw [multiset_esymm_map_mul]

/-- **The polynomial-level Weil functional equation.** If `S` is closed under the
duality `ω ↦ q/ω`, the function-field `L`-factor `∏_{ω∈S}(1 − ωT)` is **invariant**
under the substitution `ω ↦ q/ω`: `∏(1 − ωT) = ∏(1 − (q/ω)T)`. This is the
`L`-polynomial's fixedness under the FE — the `q`-weighted analog of the unitary
self-duality `LocalFactorDuality.selfDual_localFactor_eq`. -/
theorem functionField_localFactor_FE (q : ℂ) (S : Multiset ℂ)
    (hclosed : S.map (fun ω => q / ω) = S) :
    (S.map (fun ω => 1 - Polynomial.C ω * Polynomial.X)).prod
      = (S.map (fun ω => 1 - Polynomial.C (q / ω) * Polynomial.X)).prod := by
  conv_lhs => rw [← hclosed, Multiset.map_map]
  rfl

end

end GaloisForLFunctions
