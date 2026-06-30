import GaloisForLFunctions.Core

/-!
# The determinant criterion of the multiplicity estimate (Tier A)

`dss-multiplicity-estimate-spectral-genericity.md` §2, Prop 4. The DSS multiplicity estimate asks how
many spectral points a length-`L` auxiliary `D(z) = Σ_n c_n N_n^{z}` can vanish at. Its square-case
**algebraic skeleton** is a determinant criterion: a nonzero length-`L` auxiliary vanishing at `L`
diagonal arguments `z_1,…,z_L` exists **iff** the `L×L` matrix `V_{j,n} = N_n^{z_j}` is singular.

For the field, `N_n` are the prime products (`primeProduct`, cast to `ℂ`) and `z_j = -i γ_j` are the
diagonal evaluations at the spectrum; then `V` is the nonharmonic-Fourier / generalized-Vandermonde
matrix `(N_n^{-iγ_j})`, and the multiplicity estimate becomes a lower bound on `|det V|` (the
Turán / Ingham regime — DSS draft §2). This file formalizes the elementary equivalence
(`exists nonzero vanishing auxiliary ⟺ det V = 0`); the analytic `|det V|` lower bound and the zero
count are Tier C and stay in the draft.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **The determinant criterion (DSS Prop 4).** For diagonal arguments `z : Fin L → ℂ` and
frequencies `N : Fin L → ℂ`, a nonzero coefficient vector `c` whose Dirichlet auxiliary
`Σ_n N_n^{z_j} · c_n` vanishes at every `z_j` exists **iff** the matrix `V_{j,n} = N_n^{z_j}` is
singular (`det V = 0`). With `N_n = primeProduct` and `z_j = -iγ_j`, this is the nonharmonic-Fourier
/ Vandermonde nonsingularity that the multiplicity estimate must quantify. -/
theorem multiplicity_det_criterion (L : ℕ) (z N : Fin L → ℂ) :
    (∃ c : Fin L → ℂ, c ≠ 0 ∧ ∀ j, ∑ n, (N n) ^ (z j) * c n = 0)
      ↔ (Matrix.of (fun j n => (N n) ^ (z j))).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, funext fun j => ?_⟩
    simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using h j
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun j => ?_⟩
    have := congrFun h j
    simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using this

end

end GaloisForLFunctions
