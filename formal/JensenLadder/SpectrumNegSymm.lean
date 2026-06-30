import Mathlib

/-!
# Spectrum closed under negation for a matrix similar to its negative (the ±-quadruple)

The structural skeleton of the CCM secular reconstruction's reality
(`docs/rh/hawking_positivity_mechanism_falsified_20260618.md` §5–6).

With an **even** source `u` (`u_{-i}=u_i`) and the **odd** grid `d` (`d_{-i}=-d_i`), the parity flip
`F` (`e_i ↦ e_{-i}`) conjugates the reconstruction `D′ = diag(d)(I − u 1ᵀ)` to its negative:
`F D′ F = -D′`. Hence `D′` is **similar to `-D′`**, and its spectrum is **±-symmetric**: combined
with `D′` real (conjugation-symmetric), this gives the **Klein-4 `{z, z̄, -z, -z̄}` = `½±iγ`**
quadruple structure. (Even-symmetry forces the *quadruple*; *reality* — the quadruples landing on
one axis — is the extra finite hyperbolicity, exact for ζ, proven open here.)

This file formalizes the RH-free essence: **a matrix similar to its negative has spectrum closed
under negation.** We state it as: if `S` intertwines `A` with `-A` (`S*A = (-A)*S`) and `S` is
invertible, then `det(A - μ•1) = 0 ⟹ det(A + μ•1) = 0` (μ an eigenvalue ⟹ -μ an eigenvalue).
-/

open Matrix

namespace JensenLadder

/-- **±-quadruple / spectrum closed under negation.** If `S` intertwines `A` with `-A`
(`S * A = (-A) * S`) and `S` is invertible (`IsUnit S.det`), then every eigenvalue's negative is
also an eigenvalue: `det(A - μ•1) = 0 ⟹ det(A + μ•1) = 0`. This is the abstract content of
`F D′ F = -D′` (the even-source reconstruction is similar to its negative). -/
theorem eigval_neg_symm {n : ℕ} {K : Type*} [Field K]
    (A S : Matrix (Fin n) (Fin n) K) (hS : IsUnit S.det) (hint : S * A = (-A) * S) (μ : K)
    (hμ : (A - μ • (1 : Matrix (Fin n) (Fin n) K)).det = 0) :
    (A + μ • (1 : Matrix (Fin n) (Fin n) K)).det = 0 := by
  set I := (1 : Matrix (Fin n) (Fin n) K) with hI
  have key : S * (A - μ • I) = -((A + μ • I) * S) := by
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, hint, Matrix.neg_mul]
    abel
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, hμ, mul_zero, Matrix.det_neg, Matrix.det_mul] at hdet
  have hSne : S.det ≠ 0 := hS.ne_zero
  have hsign : ((-1 : K)) ^ (Fintype.card (Fin n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h0 : (A + μ • I).det * S.det = 0 := by
    rcases mul_eq_zero.mp hdet.symm with h | h
    · exact absurd h hsign
    · exact h
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hSne

end JensenLadder
