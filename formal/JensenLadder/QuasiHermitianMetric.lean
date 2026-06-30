import Mathlib
import JensenLadder.T3T5Capstone

/-!
# Capstone input (1) from Hermitian similarity: the quasi-Hermitizing metric

The T3/T5 capstone (`T3T5Capstone.riemannHypothesis_of_packagePositivity_and_convergence`) reduces RH to
two inputs, the first being **per-scale positivity**: at every scale `n` the secular reconstruction matrix
`M n` admits a positive-definite quasi-Hermitizing metric `η` (`η.PosDef ∧ η * M = Mᴴ * η`). That input
is stated abstractly. This module discharges it from a **concrete, checkable spectral condition**:
`M n` is similar to a Hermitian matrix (the finite PT-unbroken/quasi-Hermitian condition).

The bridge is the linear-algebra fact `posDef_metric_of_realDiagonalizable`: if `M = S Λ S⁻¹` with `S`
invertible and `Λ` Hermitian, then `η = (S⁻¹)ᴴ S⁻¹` is positive definite and quasi-
Hermitizes `M` (the canonical metric `η = (S⁻¹)ᴴ S⁻¹` of `dyson_metric_typeII.py`, now proved). It then
restates the capstone with input (1) replaced by similarity to Hermitian representatives:
`riemannHypothesis_of_realDiagonalizable_and_convergence`.

**Why this is progress (RH-free).** The secular reconstruction is numerically **PT-unbroken at every
tested scale** (`docs/rh/hawking_secular_pt_metric_20260618.md`: `max|Im λ| ~ 10⁻³¹…10⁻⁴⁰`, real spectrum
for `N ≤ 12`), with the metric degenerating (`cond(η) = cond(S)² → ∞`, log₁₀ `19.8→35.2`) — the
type-II₁ no-margin. So the capstone's input (1) is now relocated to a property the construction *visibly
has at finite level*: the open RH core is precisely whether the similar-to-Hermitian/PT-unbroken condition
**survives the `n→∞` limit** despite `cond(η)→∞`. Nothing here proves that survival; it sharpens what must
be proved. RH-free.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace JensenLadder

/-- **Positive quasi-Hermitizing metric from a Hermitian similarity representative.**
If `M = S * Λ * S⁻¹` with `S` invertible and `Λ` Hermitian, then
`η := (S⁻¹)ᴴ * S⁻¹` is positive definite and quasi-Hermitizes `M`: `η * M = Mᴴ * η`. This is the
canonical positive metric of a finite PT-unbroken/quasi-Hermitian operator; it supplies the capstone's input (1)
from similarity to a Hermitian representative. RH-free. -/
theorem posDef_metric_of_realDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    (M S Λ : Matrix n n ℂ) (hS : IsUnit S.det) (hΛ : Λᴴ = Λ)
    (hM : M = S * Λ * S⁻¹) :
    ∃ η : Matrix n n ℂ, η.PosDef ∧ η * M = Mᴴ * η := by
  have hzS : S.det ≠ 0 := hS.ne_zero
  have hzInv : (S⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hzS
  have hinvmul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
  have hct : Sᴴ * (S⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinvmul, Matrix.conjTranspose_one]
  refine ⟨(S⁻¹)ᴴ * S⁻¹, ?_, ?_⟩
  · have hpsd : (((S⁻¹)ᴴ) * S⁻¹).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self (S⁻¹)
    have hdet : (((S⁻¹)ᴴ) * S⁻¹).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
      exact mul_ne_zero (star_ne_zero.mpr hzInv) hzInv
    exact (hpsd.posDef_iff_det_ne_zero).mpr hdet
  · have hMH : Mᴴ = (S⁻¹)ᴴ * (Λ * Sᴴ) := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hΛ]
    calc ((S⁻¹)ᴴ * S⁻¹) * M
        = (S⁻¹)ᴴ * ((S⁻¹ * S) * (Λ * S⁻¹)) := by rw [hM]; simp only [Matrix.mul_assoc]
      _ = (S⁻¹)ᴴ * (Λ * S⁻¹) := by rw [hinvmul, Matrix.one_mul]
      _ = (S⁻¹)ᴴ * (Λ * (Sᴴ * (S⁻¹)ᴴ) * S⁻¹) := by rw [hct]; simp only [Matrix.mul_one]
      _ = Mᴴ * ((S⁻¹)ᴴ * S⁻¹) := by rw [hMH]; simp only [Matrix.mul_assoc]

/-- **T3/T5 capstone, strengthened: RH from Hermitian similarity + convergence.**
If the scale-indexed secular matrices `M n` are each similar to a Hermitian matrix
(`M n = S Λ S⁻¹`, `S` invertible, `Λ` Hermitian — finite PT-unbrokenness), and the characteristic polynomials
converge locally uniformly to `xiEntire`, then RH holds. Input (1) of the capstone is discharged here from
the concrete spectral condition via `posDef_metric_of_realDiagonalizable`; the remaining open core is that
this Hermitian-similarity condition survives the `n→∞` limit (the no-margin). It proves RH *from* these; not them. -/
theorem riemannHypothesis_of_realDiagonalizable_and_convergence
    {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (M : ∀ n, Matrix (ι n) (ι n) ℂ) (F : ℕ → ℂ → ℂ)
    (hF : ∀ n z, F n z = (M n - z • (1 : Matrix (ι n) (ι n) ℂ)).det)
    (hdiag : ∀ n, ∃ S Λ : Matrix (ι n) (ι n) ℂ, IsUnit S.det ∧ Λᴴ = Λ ∧ M n = S * Λ * S⁻¹)
    (hconv : TendstoLocallyUniformlyOn F HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis := by
  refine T3T5Capstone.riemannHypothesis_of_packagePositivity_and_convergence M F hF ?_ hconv
  intro n
  obtain ⟨S, Λ, hSu, hΛ, hMeq⟩ := hdiag n
  exact posDef_metric_of_realDiagonalizable (M n) S Λ hSu hΛ hMeq

end JensenLadder
