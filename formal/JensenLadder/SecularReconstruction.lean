import Mathlib
import JensenLadder.HurwitzRealRootedLimit

/-!
# Secular (Cauchy/Aronszajn) structure of the CCM-route spectral reconstruction

The CCM/Suzuki spectral-identification route reconstructs the zero data of `Ξ`
from a finite approximant by diagonalising a matrix of the shape
`M = diagonal d - vecMulVec (fun i => d i * u i) 1`,
a **rank-one update of a diagonal** (here `d i = 2πi/L` is the frequency grid and
`u` is the normalised bottom eigenvector of the finite Weil form).  This module
records the exact algebraic identity behind that reconstruction:

```text
det (M - z • 1) = (∏ i, (d i - z)) * (1 - ∑ i, (d i * u i) / (d i - z)).
```

Hence, off the grid `{d i}`, `z` is an eigenvalue of `M` **iff** it solves the
**secular equation** `∑ i, (d i u i)/(d i - z) = 1` — a finite Cauchy/Aronszajn
analogue of the Hadamard partial fraction `Ξ'/Ξ (s) = ∑_ρ 1/(s - ρ)`.

This makes precise the structural content of the numerical worklog entry C-D8
(`docs/rh/dyson_compute_fake_separators_20260617.md`): the abstract convergence
row `convergesToXi` of `CVSSpectralRoute`, *along this reconstruction route*, is a
statement that the secular roots converge to `{γ_n}`, with a separate
well-posedness gate `∑ vec ≠ 0`. Odd source vectors on the sign-symmetric grid
fail that gate; even source vectors additionally give the `z ↔ -z` symmetry below.

Evidence class: formal/structural identity (pure linear algebra: the matrix
determinant lemma for a diagonal plus a rank-one-with-constant-row update).  It
does NOT prove the secular roots converge, does NOT define or discharge
`convergesToXi`, and does NOT prove RH.  Theorem M is proven, but Theorem M does
not prove RH by itself.
-/

namespace JensenLadder
namespace SecularReconstruction

open Matrix
open scoped Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [Field 𝕜]

/-- Matrix determinant lemma, diagonal + rank-one-with-constant-row form:
`det (diagonal a - vecMulVec b 1) = (∏ i, a i) * (1 - ∑ i, b i / a i)`. -/
theorem secular_det (a b : n → 𝕜) (ha : ∀ i, a i ≠ 0) :
    (Matrix.diagonal a - Matrix.vecMulVec b (fun _ => (1 : 𝕜))).det
      = (∏ i, a i) * (1 - ∑ i, b i / a i) := by
  classical
  set A : Matrix n n 𝕜 := Matrix.diagonal a with hA
  set Ainv : Matrix n n 𝕜 := Matrix.diagonal (fun i => (a i)⁻¹) with hAinv
  set X : Matrix n n 𝕜 := Matrix.vecMulVec b (fun _ => (1 : 𝕜)) with hX
  have hinv : A * Ainv = 1 := by
    rw [hA, hAinv, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => a i * (a i)⁻¹) = (fun _ => (1 : 𝕜)) from
      funext fun i => mul_inv_cancel₀ (ha i)]
    simp [Matrix.diagonal_one]
  have hfactor : A - X = A * (1 - Ainv * X) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [hfactor, Matrix.det_mul]
  have hdetA : A.det = ∏ i, a i := by rw [hA, Matrix.det_diagonal]
  rw [hdetA]
  congr 1
  have hXcr : X = Matrix.replicateCol (Fin 1) b * Matrix.replicateRow (Fin 1) (fun _ => (1 : 𝕜)) := by
    rw [hX]; exact Matrix.vecMulVec_eq (Fin 1) b _
  rw [hXcr, ← Matrix.mul_assoc]
  set P : Matrix n (Fin 1) 𝕜 := Ainv * Matrix.replicateCol (Fin 1) b with hP
  set Q : Matrix (Fin 1) n 𝕜 := Matrix.replicateRow (Fin 1) (fun _ => (1 : 𝕜)) with hQ
  rw [Matrix.det_one_sub_mul_comm, Matrix.det_fin_one]
  rw [Matrix.sub_apply, Matrix.one_apply_eq]
  congr 1
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hQi : Q 0 i = 1 := by rw [hQ, Matrix.replicateRow_apply]
  have hPi : P i 0 = (a i)⁻¹ * b i := by
    rw [hP, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hAinv, Matrix.diagonal_apply_eq, Matrix.replicateCol_apply]
    · intro j _ hji
      rw [hAinv, Matrix.diagonal_apply_ne _ (Ne.symm hji), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hQi, hPi, one_mul, div_eq_inv_mul]

omit [Fintype n] in
/-- Helper: `diagonal d - z • 1 = diagonal (fun i => d i - z)`. -/
theorem diagonal_sub_smul_one (d : n → 𝕜) (z : 𝕜) :
    Matrix.diagonal d - z • (1 : Matrix n n 𝕜) = Matrix.diagonal (fun i => d i - z) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h; simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.sub_apply]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.sub_apply]

/-- Reconstruction characteristic polynomial = secular factorization.
For the reconstruction matrix `M = diagonal d - vecMulVec (fun i => d i * u i) 1`,
`det (M - z • 1) = (∏ (d i - z)) * (1 - ∑ (d i u i)/(d i - z))`. -/
theorem reconstruction_charpoly (d u : n → 𝕜) (z : 𝕜) (hz : ∀ i, d i - z ≠ 0) :
    (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜))
        - z • (1 : Matrix n n 𝕜)).det
      = (∏ i, (d i - z)) * (1 - ∑ i, (d i * u i) / (d i - z)) := by
  have hrw :
      Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜))
          - z • (1 : Matrix n n 𝕜)
        = Matrix.diagonal (fun i => d i - z)
          - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜)) := by
    rw [sub_right_comm, diagonal_sub_smul_one]
  rw [hrw, secular_det (fun i => d i - z) (fun i => d i * u i) hz]

/-- The secular criterion: off the grid `{d i}`, `z` is an eigenvalue of the
reconstruction matrix iff it solves the secular equation
`∑ (d i u i)/(d i - z) = 1`. -/
theorem isEigenvalue_iff_secular (d u : n → 𝕜) (z : 𝕜) (hz : ∀ i, d i - z ≠ 0) :
    (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜))
        - z • (1 : Matrix n n 𝕜)).det = 0
      ↔ (∑ i, (d i * u i) / (d i - z)) = 1 := by
  rw [reconstruction_charpoly d u z hz]
  have hprod : (∏ i, (d i - z)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hprod
    · exact (sub_eq_zero.mp h).symm
  · intro h; right; rw [h]; ring

omit [DecidableEq n] in
/-- For an even bottom vector on a sign-symmetric grid, the secular sum is even in `z`. -/
theorem secular_sum_neg (σ : n ≃ n) (d u : n → 𝕜) (z : 𝕜)
    (hd : ∀ i, d (σ i) = - d i) (hu : ∀ i, u (σ i) = u i) :
    (∑ i, d i * u i / (d i - z)) = (∑ i, d i * u i / (d i - -z)) := by
  rw [← Equiv.sum_comp σ (fun i => d i * u i / (d i - z))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hd, hu]
  rw [show (-d i) * u i = -(d i * u i) from by ring,
      show (-d i) - z = -(d i + z) from by ring,
      neg_div_neg_eq,
      show d i - -z = d i + z from by ring]

/-- Even bottom vector ⟹ the reconstruction spectrum is symmetric about `0`
(`z` is an eigenvalue iff `-z` is) — the formal mirror of the `γ ↔ -γ` symmetry
of `Ξ`'s zeros. This is a positive implication; an odd source vector simply does
not satisfy the hypothesis. -/
theorem reconstruction_spectrum_symmetric (σ : n ≃ n) (d u : n → 𝕜) (z : 𝕜)
    (hd : ∀ i, d (σ i) = - d i) (hu : ∀ i, u (σ i) = u i)
    (hz : ∀ i, d i - z ≠ 0) (hz' : ∀ i, d i - -z ≠ 0) :
    (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜))
        - z • (1 : Matrix n n 𝕜)).det = 0
      ↔ (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜))
        - (-z) • (1 : Matrix n n 𝕜)).det = 0 := by
  rw [isEigenvalue_iff_secular d u z hz, isEigenvalue_iff_secular d u (-z) hz',
      secular_sum_neg σ d u z hd hu]

omit [DecidableEq n] in
/-- Odd source counterpart: for an ODD source vector on a sign-symmetric grid
(`u (σ i) = - u i`), the secular sum is ODD in `z` (`S(z) = - S(-z)`).  Hence the
`z ↔ -z` eigenvalue symmetry of `reconstruction_spectrum_symmetric` FAILS for an
odd source: if `S(z) = 1` then `S(-z) = -1 ≠ 1`.  (The even/odd dichotomy is the
formal content of worklog C-D7/C-D10.) -/
theorem secular_sum_neg_odd (σ : n ≃ n) (d u : n → 𝕜) (z : 𝕜)
    (hd : ∀ i, d (σ i) = - d i) (hu : ∀ i, u (σ i) = - u i) :
    (∑ i, d i * u i / (d i - z)) = - (∑ i, d i * u i / (d i - -z)) := by
  rw [← Equiv.sum_comp σ (fun i => d i * u i / (d i - z)), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hd, hu]
  rw [show (-d i) * (-u i) = d i * u i from by ring,
      show (-d i) - z = -(d i + z) from by ring,
      div_neg,
      show d i - -z = d i + z from by ring]

/-- The reconstruction matrix `M = diagonal d - vecMulVec (fun i => d i * u i) 1`
is **pseudo-Hermitian** with respect to the explicit diagonal metric
`C = diagonal (fun i => (d i * u i)⁻¹)`:  `C * M = Mᵀ * C`.  The metric's signature
is `sign (d i * u i)` on any index set satisfying the nonzero hypothesis.  The full
CCM grid `{-N,...,N}` contains the zero frequency `d 0 = 0`, so this theorem applies
only after separating the forced zero mode, passing to a nonzero-frequency block, or
using an index set with `d i * u i ≠ 0` for every `i`.  It is the finite algebraic
handle for the PT/pseudo-Hermitian reading, not by itself a proof of real spectrum.
(Existence of `C` requires `d i * u i ≠ 0` for all `i`.) -/
theorem pseudo_hermitian (d u : n → 𝕜) (h : ∀ i, d i * u i ≠ 0) :
    (Matrix.diagonal (fun i => (d i * u i)⁻¹))
        * (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜)))
      = (Matrix.diagonal d - Matrix.vecMulVec (fun i => d i * u i) (fun _ => (1 : 𝕜)))ᵀ
        * (Matrix.diagonal (fun i => (d i * u i)⁻¹)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply, mul_one]
  rcases eq_or_ne i j with hij | hij
  · subst hij; exact mul_comm _ _
  · rw [if_neg hij, if_neg (Ne.symm hij), zero_sub, zero_sub,
        mul_neg, neg_mul, inv_mul_cancel₀ (h i), mul_inv_cancel₀ (h j)]

/-- `z ↦ det (M₀ - z • 1)` is entire (a polynomial in `z`): each matrix entry is
affine in `z`, so the Leibniz expansion of the determinant is differentiable.
This makes the secular characteristic polynomial a valid (entire) approximant for
the atlas Hurwitz RH-reduction. -/
theorem detSubSmul_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M0 : Matrix ι ι ℂ) :
    Differentiable ℂ (fun z : ℂ => (M0 - z • (1 : Matrix ι ι ℂ)).det) := by
  simp_rw [Matrix.det_apply]
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_smul
  apply Differentiable.fun_finsetProd
  intro i _
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : σ i = i <;>
    simp only [h, if_true, if_false, mul_one, mul_zero, sub_zero] <;> fun_prop

/-- **Secular-route RH reduction.**  Wires the secular reconstruction into the
atlas Hurwitz RH-reduction (`HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire`):
a scale-indexed family `F` of secular characteristic polynomials
`F n z = det (M n - z • 1)` that is (i) real-rooted and (ii) converges locally
uniformly to `xiEntire` proves RH.  The ENTIRE-NESS input is discharged here by
`detSubSmul_differentiable`, so only the two genuinely-analytic inputs remain:
`hreal` (real-rootedness of the secular characteristic polynomials; on nonzero-frequency
blocks satisfying the metric hypothesis this has the pseudo-Hermitian handle
`pseudo_hermitian`; the off-grid roots solve `isEigenvalue_iff_secular`) and
`hconv` (the spectral-identification / `convergesToXi` row).  This does NOT prove
either open input and does NOT prove RH. -/
theorem riemannHypothesis_of_secularCharpoly
    {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (M : ∀ n, Matrix (ι n) (ι n) ℂ)
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n z, F n z = (M n - z • (1 : Matrix (ι n) (ι n) ℂ)).det)
    (hreal : ∀ n z, F n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn F HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis := by
  apply HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire F _ hreal hconv
  intro n
  have hFeq : F n = fun z => (M n - z • (1 : Matrix (ι n) (ι n) ℂ)).det := funext (hF n)
  rw [hFeq]
  exact ((detSubSmul_differentiable (M n)).differentiableOn).analyticOnNhd isOpen_univ

/-- A matrix admitting a positive-definite quasi-Hermitizing metric is real-rooted:
if `η > 0` (PosDef) and `η M = Mᴴ η`, then every root of `det(M - z•1)` is real.
(Classical η-inner-product argument: an eigenvector `v` gives
`z·(vᴴηv) = vᴴη(Mv) = vᴴ(Mᴴη)v = (Mv)ᴴηv = z̄·(vᴴηv)`, and `vᴴηv > 0`.)
This is the reality criterion in Object-X form: real spectrum ⟸ a positive
quasi-Hermitizing metric `C>0` (the CPT-structure face). -/
theorem realRooted_of_quasiHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M η : Matrix ι ι ℂ) (hη : η.PosDef) (hqh : η * M = Mᴴ * η)
    (z : ℂ) (hz : (M - z • (1 : Matrix ι ι ℂ)).det = 0) :
    z.im = 0 := by
  obtain ⟨v, hv0, hker⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hz
  have hMv : M *ᵥ v = z • v := by
    have h : (M - z • (1 : Matrix ι ι ℂ)) *ᵥ v = M *ᵥ v - z • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hker] at h
    exact (sub_eq_zero.mp h.symm)
  have hpos : 0 < star v ⬝ᵥ η *ᵥ v := hη.dotProduct_mulVec_pos hv0
  have hcne : star v ⬝ᵥ η *ᵥ v ≠ 0 := hpos.ne'
  have e1 : star v ⬝ᵥ η *ᵥ (M *ᵥ v) = z * (star v ⬝ᵥ η *ᵥ v) := by
    rw [hMv, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have e2 : star v ⬝ᵥ η *ᵥ (M *ᵥ v) = star z * (star v ⬝ᵥ η *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hqh, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.star_mulVec, hMv, star_smul, smul_dotProduct, smul_eq_mul]
  have key : z * (star v ⬝ᵥ η *ᵥ v) = star z * (star v ⬝ᵥ η *ᵥ v) := e1 ▸ e2
  have hz_eq : z = star z := mul_right_cancel₀ hcne key
  have him : z.im = -z.im := by
    have h := congrArg Complex.im hz_eq
    simpa using h
  linarith

/-- **Secular-route RH reduction, Object-X form.**  RH follows once the secular
characteristic polynomials converge to `xiEntire` and each scale's reconstruction
admits a positive-definite quasi-Hermitizing metric `η` (Object X's `C>0` /
CPT-metric face).  The reality input of `riemannHypothesis_of_secularCharpoly` is
discharged by `realRooted_of_quasiHermitian`, so the open surface is exactly:
(i) a per-scale positive metric, and (ii) convergence to `Ξ`. -/
theorem riemannHypothesis_of_secularCharpoly_quasiHermitian
    {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (M : ∀ n, Matrix (ι n) (ι n) ℂ)
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n z, F n z = (M n - z • (1 : Matrix (ι n) (ι n) ℂ)).det)
    (hqh : ∀ n, ∃ η : Matrix (ι n) (ι n) ℂ, η.PosDef ∧ η * (M n) = (M n)ᴴ * η)
    (hconv : TendstoLocallyUniformlyOn F HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secularCharpoly M F hF _ hconv
  intro n z hz
  obtain ⟨η, hηpd, hηqh⟩ := hqh n
  rw [hF] at hz
  exact realRooted_of_quasiHermitian (M n) η hηpd hηqh z hz

end SecularReconstruction
end JensenLadder
