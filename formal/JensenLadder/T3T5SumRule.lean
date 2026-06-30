import Mathlib

/-!
# The Sherman–Morrison no-margin sum rule (Stage 0/2 refinement of the T3/T5 program)

This formalizes the determinant identities behind the **scalar no-margin sum rule** found in
`docs/rh/dyson_critical_coupling_attempt_20260618.md` §7.  The finite Weil form on the even
sector is `QW = ρ·uuᵀ − (W_R+P)` where `ρ·uuᵀ = W0_2` is the **rank-1** archimedean main term
(`u` = the archimedean mode `1/(L²+16π²n²)`) and `M = W_R+P` is the intersection form.  Because
the archimedean reference is rank-one, the no-margin (`det QW = 0`) is a **scalar** condition via
the matrix-determinant / Sherman–Morrison lemma:

`det(M − ρ·uuᵀ) = det M · (1 − ρ·uᵀM⁻¹u)`,  so  `det QW = 0 ⟺ S := ρ·uᵀM⁻¹u = 1`.

Numerically (worklog §7): for ζ, `S → 1⁺` (the rank-1 archimedean lift asymptotically saturates
the Hodge-index threshold = the no-margin); the no-margin is this single resolvent number's
distance to the critical value `1` (= the Aubry–André / BPS critical coupling, in resolvent form).

Mathlib has the special diagonal case (`SecularReconstruction.secular_det`) but not the general
rank-one / Sherman–Morrison determinant lemma; this module supplies it.  Evidence class: linear
algebra over a field, axiom-clean.  Does NOT prove `S ≥ 1` in the limit (= RH).
-/

namespace JensenLadder
namespace T3T5SumRule

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [Field 𝕜]

/-- **Rank-one determinant lemma:** `det(1 − a bᵀ) = 1 − b · a`. -/
theorem rankOne_det (a b : n → 𝕜) :
    (1 - Matrix.vecMulVec a b).det = 1 - b ⬝ᵥ a := by
  rw [Matrix.vecMulVec_eq (Fin 1) a b, Matrix.det_one_sub_mul_comm]
  simp [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply, dotProduct,
        mul_comm]

/-- **Sherman–Morrison determinant** (general invertible `M`):
`det(M − a bᵀ) = det M · (1 − b · (M⁻¹ a))`. -/
theorem shermanMorrison_det (M : Matrix n n 𝕜) (hM : IsUnit M.det) (a b : n → 𝕜) :
    (M - Matrix.vecMulVec a b).det = M.det * (1 - b ⬝ᵥ (M⁻¹ *ᵥ a)) := by
  have hfac : M - Matrix.vecMulVec a b = M * (1 - Matrix.vecMulVec (M⁻¹ *ᵥ a) b) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  rw [hfac, Matrix.det_mul, rankOne_det]

/-- **The no-margin sum rule (threshold form).**  For the finite Weil form
`QW = ρ·uuᵀ − M` (rank-1 archimedean lift `ρ·uuᵀ` minus the intersection form `M`),
`det QW = 0 ⟺ S = 1`, where `S := ρ·uᵀM⁻¹u`.  Equivalently the determinant equals
`(-1)^card · det M · (1 − S)`, so the bottom eigenvalue crosses zero exactly at the
critical value `S = 1` (= the no-margin). -/
theorem nomargin_det (M : Matrix n n 𝕜) (hM : IsUnit M.det) (u : n → 𝕜) (ρ : 𝕜) :
    (ρ • Matrix.vecMulVec u u - M).det
      = (-1) ^ Fintype.card n * (M.det * (1 - ρ * (u ⬝ᵥ (M⁻¹ *ᵥ u)))) := by
  have hsmul : ρ • Matrix.vecMulVec u u = Matrix.vecMulVec (ρ • u) u := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hneg : ρ • Matrix.vecMulVec u u - M = -(M - Matrix.vecMulVec (ρ • u) u) := by
    rw [hsmul]; abel
  rw [hneg, Matrix.det_neg, shermanMorrison_det M hM (ρ • u) u, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]

/-- The threshold itself: with `M` invertible, the Weil determinant vanishes iff the scalar
sum rule sits exactly at the critical value `S = ρ·uᵀM⁻¹u = 1`. -/
theorem nomargin_threshold (M : Matrix n n 𝕜) (hM : IsUnit M.det) (u : n → 𝕜) (ρ : 𝕜) :
    (ρ • Matrix.vecMulVec u u - M).det = 0 ↔ ρ * (u ⬝ᵥ (M⁻¹ *ᵥ u)) = 1 := by
  rw [nomargin_det M hM u ρ]
  have h1 : ((-1) ^ Fintype.card n : 𝕜) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : M.det ≠ 0 := hM.ne_zero
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h h1
    · exact absurd h h2
    · exact (sub_eq_zero.mp h).symm
  · intro h; right; right; rw [h]; ring
end T3T5SumRule
end JensenLadder
