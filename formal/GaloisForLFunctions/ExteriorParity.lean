import Mathlib

/-!
# Exterior-power σ-parity (Tier A)

This file formalizes the cohomological grading of branch B5
(`difference-galois-cohomology.md` §3): the functional-equation involution `σ`
acts as `−1` on the prime lattice `V = H¹`, hence as `(−1)ᵏ` on `∧ᵏV = Hᵏ`.

Concretely: for any scalar `c` and any module `M`, the induced map of `c • id`
on the `n`-th exterior power `⋀ⁿM` is `cⁿ • id`; specializing to `c = −1` gives
the parity `∧ⁿ(−id) = (−1)ⁿ • id`. With `σ = −1` on `V` this is the cohomological
`σ|_{∧ᵏV} = (−1)ᵏ` grading — the exterior-power form of the FE parity that
`FunctionalEquationParity.lean` records at the moment level.

This is the elementary functoriality of the exterior power on scalar maps; it
does not formalize the full `G_L`-cohomology ring, the cup product, or the
monoidality obstruction `ω ∈ H²` (the wall).
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **B5 §3 (exterior-power scaling).** The induced map of the scalar map
`c • id` on the `n`-th exterior power `⋀ⁿM` is `cⁿ • id`: the alternating
`n`-linear structure pulls the scalar out of all `n` slots. -/
theorem exteriorPower_map_smul_id (n : ℕ) (c : R) :
    exteriorPower.map n (c • LinearMap.id : M →ₗ[R] M) = c ^ n • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext m
  have hsmul : (exteriorPower.ιMulti R n) (fun i => c • m i)
      = (∏ _i : Fin n, c) • (exteriorPower.ιMulti R n) m :=
    (exteriorPower.ιMulti R n).map_smul_univ (fun _ => c) m
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Function.comp_def, hsmul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **B5 §3 (cohomological FE σ-parity).** With `σ = −1` on the prime lattice
`V`, the induced map on `∧ⁿV = Hⁿ` is `(−1)ⁿ • id`: `σ|_{∧ⁿV} = (−1)ⁿ`. This is
the exterior-power form of the functional-equation moment parity. -/
theorem exteriorPower_map_neg_id (n : ℕ) :
    exteriorPower.map n (-LinearMap.id : M →ₗ[R] M) = (-1 : R) ^ n • LinearMap.id := by
  have h := exteriorPower_map_smul_id (R := R) (M := M) n (-1)
  simpa using h

end

end GaloisForLFunctions
