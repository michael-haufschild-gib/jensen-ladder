import Mathlib

/-!
# Cayley bridge: η-self-adjoint ⟹ η-unitary Cayley transform (the linear/blind-side unification)

Two independently developed reductions of RH converge on one finite-level object:

* **Quasi-Hermitizing metric** (`JensenLadder.QuasiHermitianMetric`, capstone input (1)): the secular
  reconstruction `Mₙ` admits a positive metric `η` with `η Mₙ = Mₙᴴ η` (i.e. `Mₙ` is self-adjoint in the
  `η`-inner-product — PT-unbroken).
* **Li / HP-Cayley** (berry, `LiCayleyAtom`): RH ⟺ the Cayley operator `C` (with `w = 1 − 1/ρ`, the FE
  acting as `w ↦ 1/w`) is **unitary**.

This module proves they are the **same statement** at finite level: if `η M = Mᴴ η` and `M + i` is
invertible, then the Cayley transform `C = (M − i)(M + i)⁻¹` is **`η`-unitary**, `Cᴴ η C = η`. So a positive
quasi-Hermitizing metric (input (1)) is exactly a unitary Cayley transform in that metric (HP-Cayley) —
the two routes unify.

**Honest scope — this is the BLIND side.** Unitarity / the Cayley transform is a *linear/unitary*
invariant, and that invariant is RH-blind: it certifies the spectrum is real (PT-unbroken) but says nothing
about *which* reals — it does not identify the spectrum with the zeros of `ξ`. The RH content lives in the
*quadratic / spectral-identification* piece — the convergence input (capstone input (2),
`Fₙ → xiEntire`), that the operator's spectrum actually **is** the zero set. This bridge consolidates the
two reductions' *blind* halves into one; it does not touch the identification half. RH-free.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace JensenLadder

/-- **Cayley transform of an η-self-adjoint operator is η-unitary.**
If `η M = Mᴴ η` (M self-adjoint in the η-inner-product) and `M + i` is invertible, then the Cayley
transform `C = (M − i)(M + i)⁻¹` satisfies `Cᴴ η C = η` — `C` is unitary in the η-inner-product. Unifies the
quasi-Hermitizing metric `η` (capstone input (1)) with the Cayley-unitary (Li/HP-Cayley) formulation.
The unitary invariant is RH-blind (certifies real spectrum, not the spectral identification); RH-free. -/
theorem cayley_etaUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (M η : Matrix n n ℂ) (hsa : η * M = Mᴴ * η)
    (hA : IsUnit (M + Complex.I • (1 : Matrix n n ℂ)).det) :
    ((M - Complex.I • (1 : Matrix n n ℂ)) * (M + Complex.I • (1 : Matrix n n ℂ))⁻¹)ᴴ *
        (η * ((M - Complex.I • (1 : Matrix n n ℂ)) *
          (M + Complex.I • (1 : Matrix n n ℂ))⁻¹)) = η := by
  set A := M + Complex.I • (1 : Matrix n n ℂ) with hAdef
  set B := M - Complex.I • (1 : Matrix n n ℂ) with hBdef
  have hAH : Aᴴ = Mᴴ - Complex.I • (1 : Matrix n n ℂ) := by
    rw [hAdef]
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hBH : Bᴴ = Mᴴ + Complex.I • (1 : Matrix n n ℂ) := by
    rw [hBdef]
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hAint : Bᴴ * η = η * A := by
    rw [hBH, hAdef, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hsa]
  have hBint : η * B = Aᴴ * η := by
    rw [hAH, hBdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hsa]
  have hc : Commute (Complex.I • (1 : Matrix n n ℂ)) M := (Commute.one_left M).smul_left Complex.I
  have hcomm : A * B = B * A := by
    rw [hAdef, hBdef]
    exact (((Commute.refl M).sub_right hc.symm).add_left (hc.sub_right (Commute.refl _))).eq
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAHdet : IsUnit (Aᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  have hAHinv : (Aᴴ)⁻¹ * Aᴴ = 1 := Matrix.nonsing_inv_mul Aᴴ hAHdet
  have hCH : ((B * A⁻¹))ᴴ = (Aᴴ)⁻¹ * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  rw [hCH]
  calc (Aᴴ)⁻¹ * Bᴴ * (η * (B * A⁻¹))
      = (Aᴴ)⁻¹ * (Bᴴ * η) * (B * A⁻¹) := by simp only [Matrix.mul_assoc]
    _ = (Aᴴ)⁻¹ * (η * A) * (B * A⁻¹) := by rw [hAint]
    _ = (Aᴴ)⁻¹ * (η * (A * B) * A⁻¹) := by simp only [Matrix.mul_assoc]
    _ = (Aᴴ)⁻¹ * (η * (B * A) * A⁻¹) := by rw [hcomm]
    _ = (Aᴴ)⁻¹ * (η * B * (A * A⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = (Aᴴ)⁻¹ * (η * B) := by rw [hAinv, Matrix.mul_one]
    _ = (Aᴴ)⁻¹ * (Aᴴ * η) := by rw [hBint]
    _ = η := by rw [← Matrix.mul_assoc, hAHinv, Matrix.one_mul]

end JensenLadder
