import Mathlib

/-!
# DSS determinant criterion: finite linear algebra skeleton

This file formalizes the Tier-A algebraic skeleton from
`docs/drafts/dss-multiplicity-estimate-spectral-genericity.md` §2:
a nonzero auxiliary coefficient vector vanishing at all sample points exists
exactly when the associated square complex matrix is singular.

It deliberately does not formalize DSS, zeta-zero separation, determinant lower
bounds, least singular values, or RH. The ledger here is only finite-dimensional
linear algebra over `ℂ`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A square complex matrix has a nontrivial kernel vector exactly when its
determinant vanishes. This is the finite algebra behind the DSS determinant
criterion. -/
theorem matrix_nontrivial_kernel_iff_det_eq_zero {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) :
    (∃ c : Fin n → ℂ, c ≠ 0 ∧ V.mulVec c = 0) ↔ V.det = 0 := by
  constructor
  · rintro ⟨c, hc0, hc⟩
    by_contra hdet
    have hker : LinearMap.ker (Matrix.toLin' V) = ⊥ := by
      simpa using
        Matrix.ker_toLin_eq_bot (Pi.basisFun ℂ (Fin n)) V (isUnit_iff_ne_zero.mpr hdet)
    have hcKer : c ∈ LinearMap.ker (Matrix.toLin' V) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hc
    have hcZero : c = 0 := by
      have : c ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := by
        simpa [hker] using hcKer
      simpa using this
    exact hc0 hcZero
  · intro hdet
    have hk : ⊥ < LinearMap.ker (Matrix.toLin' V) := by
      exact LinearMap.bot_lt_ker_of_det_eq_zero (by rwa [LinearMap.det_toLin'])
    rcases SetLike.exists_of_lt hk with ⟨c, hcKer, hcBot⟩
    refine ⟨c, ?_, ?_⟩
    · intro hcZero
      apply hcBot
      simp [hcZero]
    · have hcLin : (Matrix.toLin' V) c = 0 := LinearMap.mem_ker.mp hcKer
      rwa [Matrix.toLin'_apply] at hcLin

end

end GaloisForLFunctions
