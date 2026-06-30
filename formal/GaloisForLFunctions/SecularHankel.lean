import GaloisForLFunctions.Core

/-!
# Finite secular Hankel positivity: real spectrum ⟹ PSD moment Gram

The secular-positivity drafts use the Hermite/Hankel face of RH: a moment Hankel matrix built from
the squared-zero power sums is positive semidefinite when the underlying finite spectrum is real.

This file formalizes only the finite, elementary, forward direction. Given real points `t_i`, the
Hankel matrix

`H_{jk} = Σ_i t_i^(j+k)`

is the Gram matrix `B Bᴴ` with `B_{j,i}=t_i^j`, hence is positive semidefinite. No converse, infinite
moment problem, zero counting, or RH statement is formalized here.
-/

open scoped BigOperators ComplexOrder

open Matrix

namespace GaloisForLFunctions

noncomputable section

/-- **Finite Hermite/Hankel Gram positivity.** For a finite real spectrum `t : Fin n → ℝ`, the
complex Hankel moment matrix `H_{jk}=Σ_i t_i^(j+k)` is positive semidefinite, since it is the Gram
matrix `B Bᴴ` of the finite Vandermonde-style matrix `B_{j,i}=t_i^j`. This is the ledger-safe easy
direction of the secular Hankel/Hermite face: real finite points imply PSD Hankel moments. -/
theorem secularHankel_posSemidef {n m : ℕ} (t : Fin n → ℝ) :
    (Matrix.of (fun j k : Fin m => ∑ i, (t i : ℂ) ^ ((j : ℕ) + (k : ℕ)))).PosSemidef := by
  let B : Matrix (Fin m) (Fin n) ℂ := Matrix.of (fun j i => (t i : ℂ) ^ (j : ℕ))
  have hBB : (Matrix.of (fun j k : Fin m => ∑ i, (t i : ℂ) ^ ((j : ℕ) + (k : ℕ))))
      = B * Bᴴ := by
    ext j k
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, B, Matrix.of_apply, pow_add]
  rw [hBB]
  exact Matrix.posSemidef_self_mul_conjTranspose B

end

end GaloisForLFunctions
