import GaloisForLFunctions.Core

/-!
# The measure carrier: finite poles → infinite spectrum (Stage-2 infrastructure)

`formalization-roadmap-finite-to-apex.md` Stage 2. The infinite carrier `m_ξ(z) = -Ξ'/Ξ(z)` is, via
the Hadamard product, a regularized sum over the (infinitely many) zeros. The reusable abstract core
started here is the **finite-total-mass measure carrier** `m_μ(z) = ∫ (λ - z)⁻¹ dμ(λ)` for a measure
`μ` on `ℝ`: the finite real spectrum is the atomic case `μ = Σ_i δ_{t_i}`
(`CarrierPickKernel.real_spectrum_carrier_herglotz`), and finite measures with infinite support give
the first measure-level generalization. This is not yet the raw `ξ` zero-counting measure, which is
not finite and needs Hadamard/regularization and convergence infrastructure.

This file proves the finite-measure forward Herglotz and Pick-positivity directions. The converse
Nevanlinna/Pick theorem, Krein–Langer `N_κ` theory, and the `ξ` zero-counting specialization remain
future infrastructure bricks (Stage 2 cont.).
-/

open scoped BigOperators ComplexOrder MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- **Measure carrier is Herglotz (forward, infinite spectrum).** For a finite measure `μ` on `ℝ`, the
carrier `m_μ(z) = ∫ (λ - z)⁻¹ dμ(λ)` satisfies `Im m_μ(z) ≥ 0` on `ℂ⁺` — a Nevanlinna/Herglotz
function. Generalizes the finite real-spectrum carrier to a measure: the integrand
`Im((λ - z)⁻¹) = Im(z)/|λ - z|² ≥ 0` and the integral of a nonnegative function is nonnegative
(integrability from the bound `‖(λ - z)⁻¹‖ ≤ (Im z)⁻¹` against the finite measure). The `ξ`
zero-counting carrier requires an additional regularized/locally-finite passage and is not asserted
here. -/
theorem measure_carrier_herglotz (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (∫ lam, ((lam : ℂ) - z)⁻¹ ∂μ).im := by
  have hb : ∀ lam : ℝ, z.im ≤ ‖(lam : ℂ) - z‖ := by
    intro lam
    have h1 : |((lam : ℂ) - z).im| ≤ ‖(lam : ℂ) - z‖ := Complex.abs_im_le_norm _
    have h2 : ((lam : ℂ) - z).im = -z.im := by simp [Complex.sub_im]
    rw [h2, abs_neg, abs_of_pos hz] at h1
    exact h1
  have hbound : ∀ lam : ℝ, ‖((lam : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ := by
    intro lam
    rw [norm_inv]
    gcongr
    exact hb lam
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ := by
    apply Measurable.aestronglyMeasurable; fun_prop
  have hint : MeasureTheory.Integrable (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) μ :=
    MeasureTheory.Integrable.of_bound hmeas (z.im)⁻¹ (MeasureTheory.ae_of_all _ hbound)
  have hswap : (∫ lam, ((lam : ℂ) - z)⁻¹ ∂μ).im = ∫ lam, (((lam : ℂ) - z)⁻¹).im ∂μ := by
    rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint]; rfl
  rw [hswap]
  apply MeasureTheory.integral_nonneg
  intro lam
  show (0 : ℝ) ≤ ((lam : ℂ) - z)⁻¹.im
  rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  exact div_nonneg (le_of_lt hz) (Complex.normSq_nonneg _)

/-- **The measure Pick kernel matrix is Hermitian** (`K(w,z) = conj K(z,w)`): the symmetry half of the
infinite `K ⪰ 0`. For nodes `z : Fin n → ℂ`, the matrix `K_{jk} = ∫ (λ-z_j)⁻¹ conj((λ-z_k)⁻¹) dμ` is
Hermitian, via `star (∫ f) = ∫ star f` (`integral_conj`). -/
theorem measure_pick_isHermitian (μ : MeasureTheory.Measure ℝ) {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ)).IsHermitian := by
  ext j k
  rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun lam => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

/-- **The measure Pick kernel is positive semidefinite (finite-measure forward `K ⪰ 0`).** For a finite
measure `μ` on `ℝ` and nodes `z : Fin n → ℂ` in `ℂ⁺`, the measure Pick matrix
`K_{jk} = ∫ (λ-z_j)⁻¹ conj((λ-z_k)⁻¹) dμ` is positive semidefinite — its quadratic form is
`∫ |∑_k c_k conj((λ-z_k)⁻¹)|² dμ ≥ 0`. This is the forward finite-measure
Nevanlinna–Pick direction (the measure-carrier `K ⪰ 0`), of which the finite
`CarrierPickKernel.pick_kernel_posSemidef` is the atomic-measure shadow. -/
theorem measure_pick_posSemidef (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ)).PosSemidef := by
  have hb : ∀ (j : Fin n) (lam : ℝ), (z j).im ≤ ‖(lam : ℂ) - z j‖ := by
    intro j lam
    have h1 : |((lam : ℂ) - z j).im| ≤ ‖(lam : ℂ) - z j‖ := Complex.abs_im_le_norm _
    have h2 : ((lam : ℂ) - z j).im = -(z j).im := by simp [Complex.sub_im]
    rw [h2, abs_neg, abs_of_pos (hz j)] at h1; exact h1
  have hbd : ∀ (j : Fin n) (lam : ℝ), ‖((lam : ℂ) - z j)⁻¹‖ ≤ ((z j).im)⁻¹ := by
    intro j lam; have hzj := hz j; rw [norm_inv]; gcongr; exact hb j lam
  have hintp : ∀ j k : Fin n,
      MeasureTheory.Integrable (fun lam : ℝ => ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹)) μ := by
    intro j k
    refine MeasureTheory.Integrable.of_bound ?_ (((z j).im)⁻¹ * ((z k).im)⁻¹)
      (MeasureTheory.ae_of_all _ (fun lam => ?_))
    · apply Measurable.aestronglyMeasurable; fun_prop
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hbd j lam) (hbd k lam) (norm_nonneg _) (inv_nonneg.mpr (hz j).le)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (measure_pick_isHermitian μ z) (fun c => ?_)
  set P : ℝ → ℂ := fun lam => ∑ k, c k * star (((lam : ℂ) - z k)⁻¹) with hP
  have key : star c ⬝ᵥ (Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ)).mulVec c
      = ∫ lam, (starRingEnd ℂ) (P lam) * P lam ∂μ := by
    simp only [dotProduct]
    have hswap : ∀ j, star c j * (Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ)).mulVec c j
        = ∫ lam, ∑ k, star (c j) * (c k * (((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹))) ∂μ := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum, MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Matrix.of_apply, Pi.star_apply,
            show star (c j) * ((∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ) * c k)
              = (star (c j) * c k) * ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ from by ring,
            ← MeasureTheory.integral_const_mul]
        congr 1; ext lam; ring
      · intro k _
        exact ((hintp j k).const_mul (c k)).const_mul (star (c j))
    simp_rw [hswap]
    rw [← MeasureTheory.integral_finsetSum]
    · refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun lam => ?_))
      simp only [hP, map_sum, map_mul, RCLike.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    · intro j _
      apply MeasureTheory.integrable_finsetSum
      intro k _
      exact ((hintp j k).const_mul (c k)).const_mul (star (c j))
  rw [key]
  have hcp : ∀ lam, (starRingEnd ℂ) (P lam) * P lam = ((Complex.normSq (P lam) : ℝ) : ℂ) := by
    intro lam; rw [← Complex.normSq_eq_conj_mul_self]
  simp_rw [hcp]
  rw [integral_complex_ofReal, Complex.le_def]
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.ofReal_re]
    exact MeasureTheory.integral_nonneg (fun lam => Complex.normSq_nonneg _)
  · simp [Complex.ofReal_im]

/-- **Schur-product closure of the infinite measure Pick kernels.** The entrywise (Hadamard) product
of two measure Pick kernels (for finite measures `μ`, `ν` on the same `ℂ⁺`-nodes) is again positive
semidefinite (Schur product theorem). So the measure-carrier Pick kernels form a Schur-product
semigroup: products/tensors of Nevanlinna carriers stay Pick-positive — the infinite-spectrum analogue
of `CayleySchur.szego_hadamard_posSemidef`, built on the hard `measure_pick_posSemidef`. -/
theorem measure_pick_hadamard_posSemidef (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, 0 < (z j).im) :
    ((Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂μ)).hadamard
      (Matrix.of (fun j k => ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹) ∂ν))).PosSemidef :=
  (measure_pick_posSemidef μ z hz).hadamard (measure_pick_posSemidef ν z hz)

/-- **Finite ↔ infinite wiring: the finite carrier is the atomic-measure case.** For real nodes
`t : Fin n → ℝ`, the measure carrier of the atomic measure `μ = ∑_i δ_{t_i}` is exactly the finite
real-spectrum carrier `∑_i (t_i - z)⁻¹`. So `real_spectrum_carrier_herglotz` (and the finite Pick
results) are the atomic specializations of the measure-level theorems above. -/
theorem measure_carrier_atomic {n : ℕ} (t : Fin n → ℝ) (z : ℂ) :
    ∫ lam, ((lam : ℂ) - z)⁻¹ ∂(∑ i, MeasureTheory.Measure.dirac (t i))
      = ∑ i, (((t i : ℂ)) - z)⁻¹ := by
  rw [MeasureTheory.integral_finsetSum_measure
        (fun i _ => MeasureTheory.integrable_dirac (enorm_lt_top))]
  simp only [MeasureTheory.integral_dirac]

end

end GaloisForLFunctions
