import Mathlib

/-!
# Self-adjoint resolvent m-function is Herglotz — the correct de Branges object

`SecularHerglotz.secular_herglotz` proves the Herglotz property from *positive residues* — but the ζ-facing
`Q_W` reconstruction has a mixed-sign source, so that lemma is a positive-residue *model* (see its scope caveat).
The **fundamental** de Branges fact, which applies to the
*actual* self-adjoint (real-symmetric) `Q_W`, is this: the resolvent m-function
`m(z) = ⟨v, (A − z)⁻¹ v⟩ = vᴴ (A − z)⁻¹ v` of any self-adjoint `A` is **Herglotz** —
`Im m(z) = Im(z) · ‖(A − z)⁻¹ v‖²`, strictly positive on the upper half-plane.

Stated with the explicit solution `w = (A − z)⁻¹ v` (i.e. `(A − z) w = v`) to avoid the matrix inverse.
Mechanism: `m = wᴴ A w − conj(z) · wᴴ w`; `wᴴ A w` is real (self-adjointness), `wᴴ w = ∑‖wᵢ‖² > 0`, so
`Im m = Im(z) · ∑‖wᵢ‖²`. This is margin-free boundary/Nevanlinna structure. With
`SecularHerglotz.herglotz_real_level` it yields real spectrum from the m-function structure. RH-free. -/

open Matrix

namespace JensenLadder

/-- **Self-adjoint resolvent m-function is Herglotz.** For self-adjoint `A` (`Aᴴ = A`), `Im z > 0`, and `w`
solving `(A − z) w = v`, the m-function `m = vᴴ w` has `Im m = Im(z) · ∑‖wᵢ‖² > 0`. The correct Herglotz
object for the real-symmetric `Q_W` (not the positive-residue model). RH-free. -/
theorem selfadjoint_resolvent_herglotz {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : Aᴴ = A) (z : ℂ) (hz : 0 < z.im) (v w : n → ℂ)
    (hw : (A - z • (1 : Matrix n n ℂ)) *ᵥ w = v) (hwne : w ≠ 0) :
    0 < (star v ⬝ᵥ w).im := by
  have hQval : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
    rw [dotProduct, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  have hSpos : 0 < (∑ i, Complex.normSq (w i) : ℝ) := by
    apply Finset.sum_pos'
    · intro i _; exact Complex.normSq_nonneg _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hwne
      exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  have hPim : (star w ⬝ᵥ (A *ᵥ w)).im = 0 := by
    rw [← Complex.conj_eq_iff_im,
        show (starRingEnd ℂ) (star w ⬝ᵥ (A *ᵥ w)) = star (star w ⬝ᵥ (A *ᵥ w)) from rfl,
        ← star_dotProduct, Matrix.star_mulVec, hA, ← Matrix.dotProduct_mulVec]
  have hsplit : star w ⬝ᵥ (A *ᵥ w - star z • w)
              = star w ⬝ᵥ (A *ᵥ w) - star z * (star w ⬝ᵥ w) := by
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hm : star v ⬝ᵥ w = star w ⬝ᵥ (A *ᵥ w) - star z * (star w ⬝ᵥ w) := by
    rw [← hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.conjTranspose_sub, hA,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hsplit]
  rw [hm, hQval, Complex.sub_im, Complex.mul_im, hPim]
  simp only [Complex.star_def, Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im,
    Complex.conj_re, mul_zero, zero_add, zero_sub, neg_mul, neg_neg]
  exact mul_pos hz hSpos

/-- **Off-line atom ⟹ non-PSD moment matrix (the Hamburger falsification side).** The 2×2 moment matrix of
a conjugate-pair atomic measure `{a ± iδ}` (unit weights) is `[[2, 2a],[2a, 2(a²−δ²)]]`, with determinant
`−4δ²` — negative for `δ ≠ 0` — so it is **not** positive semidefinite. This is the complex-node complement
of the real-node moment criterion (`HermiteHankelDetector.moment_matrix_posSemidef_iff`): an off-line atom
is detected by the moment-matrix inertia (no blind spot), with the negativity scaling as `δ²` (the
margin-free near-line regime, verified numerically). RH-free. -/
theorem conj_pair_moment_not_posSemidef (a δ : ℝ) (hδ : δ ≠ 0) :
    ¬ (Matrix.of ![![(2:ℝ), 2*a], ![2*a, 2*(a^2 - δ^2)]]).PosSemidef := by
  intro h
  have hdet : (Matrix.of ![![(2:ℝ), 2*a], ![2*a, 2*(a^2 - δ^2)]]).det = -4*δ^2 := by
    rw [Matrix.det_fin_two]; simp; ring
  have hpos : 0 ≤ (Matrix.of ![![(2:ℝ), 2*a], ![2*a, 2*(a^2 - δ^2)]]).det := h.det_nonneg
  rw [hdet] at hpos
  have : 0 < δ^2 := by positivity
  nlinarith

end JensenLadder
