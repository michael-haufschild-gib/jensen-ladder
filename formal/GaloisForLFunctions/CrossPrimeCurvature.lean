import GaloisForLFunctions.Core

/-!
# Cross-prime curvature: square-zero rank-two computation

This file formalizes the nilpotent matrix algebra used in
`docs/drafts/pipeline/2-fully-proven/cross-prime-curvature-reducibility.md`.

For a rank-two unipotent extension with `E^2 = 0`, matrices have the form
`I + b E`. The paper computation of the curvature coefficient is the elementary
identity
`(I-b_qE)(I-σ_q(b_p)E)(I+b_pE)(I+σ_p(b_q)E)
  = I + (b_p + σ_p(b_q) - b_q - σ_q(b_p))E`.
-/

namespace GaloisForLFunctions

noncomputable section

open Matrix

/-- The upper-unipotent matrix `I + aE`, where `E` has a single upper-right
entry and satisfies `E^2 = 0`. -/
def upperUnipotentE (R : Type*) [CommRing R] (a : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![1, a], ![0, 1]]

/-- Multiplication law for the square-zero upper-unipotent matrices:
`(I+aE)(I+bE)=I+(a+b)E`. -/
theorem upperUnipotentE_mul {R : Type*} [CommRing R] (a b : R) :
    upperUnipotentE R a * upperUnipotentE R b = upperUnipotentE R (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotentE, Matrix.mul_apply]
  abel

/-- The rank-two nilpotent curvature identity from the cross-prime curvature
card. With `bp=b_p`, `bq=b_q`, `sp_bq=σ_p(b_q)`, and `sq_bp=σ_q(b_p)`, this is
`F_{pq}=I+((1-σ_q)b_p-(1-σ_p)b_q)E`. -/
theorem upperUnipotentE_curvature_eq {R : Type*} [CommRing R]
    (bp bq sp_bq sq_bp : R) :
    upperUnipotentE R (-bq) * upperUnipotentE R (-sq_bp) *
        upperUnipotentE R bp * upperUnipotentE R sp_bq =
      upperUnipotentE R ((bp + sp_bq) - (bq + sq_bp)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotentE, Matrix.mul_apply]
  abel

end

end GaloisForLFunctions
