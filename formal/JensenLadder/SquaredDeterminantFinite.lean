import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite squared determinant multiplicativity

This module records the finite-matrix algebra behind the squared determinant
target:

```text
  det(A - zI) det(A + zI) = det(A^2 - z^2 I).
```

For finite matrices over a commutative ring this is ordinary determinant
multiplicativity plus the centrality of scalar matrices.  This clears only the
finite SQ-1 row.  It does not construct a carrier operator, prove any
regularized determinant analogue, prove determinant convergence, or prove RH.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantFinite

open Matrix

universe u v

variable {n : Type u} {R : Type v} [CommRing R] [Fintype n] [DecidableEq n]

/-- The paired finite-matrix factors multiply to the squared shift. -/
theorem matrix_pair_product_eq_square_shift
    (A : Matrix n n R) (z : R) :
    (A - z • (1 : Matrix n n R)) * (A + z • (1 : Matrix n n R)) =
      A * A - (z ^ 2) • (1 : Matrix n n R) := by
  have hAz : A * (z • (1 : Matrix n n R)) = z • A := by
    simp
  have hzA : (z • (1 : Matrix n n R)) * A = z • A := by
    simp
  have hzz : (z • (1 : Matrix n n R)) * (z • (1 : Matrix n n R)) =
      (z ^ 2) • (1 : Matrix n n R) := by
    simp [pow_two, smul_smul]
  rw [sub_mul, mul_add, mul_add, hAz, hzA, hzz]
  abel

/-- Finite matrices satisfy the paired determinant identity for the `z^2` target. -/
theorem det_pair_mul_eq_square_shift_det
    (A : Matrix n n R) (z : R) :
    (A - z • (1 : Matrix n n R)).det *
        (A + z • (1 : Matrix n n R)).det =
      (A * A - (z ^ 2) • (1 : Matrix n n R)).det := by
  rw [← matrix_pair_product_eq_square_shift A z, Matrix.det_mul]

end SquaredDeterminantFinite
end JensenLadder
