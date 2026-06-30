import GaloisForLFunctions.Core

/-!
# The Cayley transform: Herglotz ⟷ Schur (the carrier's disk picture)

The carrier has two equivalent pictures: the **upper-half-plane / Herglotz** picture
(`m : ℂ⁺ → ℂ̄⁺`, `Im m ≥ 0`) used in `CarrierPickKernel`/`MeasureCarrier`, and the **disk / Schur**
picture (`θ : 𝔻 → 𝔻̄`, `‖θ‖ ≤ 1`) used in de Branges / Krein–Langer theory. They are exchanged by the
**Cayley transform** `θ = (m - i)/(m + i)`. This file proves the forward bridge (Herglotz ⟹ Schur),
the gateway from the carrier's Pick-positivity (`K ⪰ 0`) to the Schur/de Branges side of the field.
-/

open scoped ComplexOrder BigOperators

open Matrix

namespace GaloisForLFunctions

noncomputable section

/-- **Cayley transform: a Herglotz value maps into the closed unit disk (Schur).** If `Im m ≥ 0`
then `‖(m - i)/(m + i)‖ ≤ 1`. (Reason: `‖m + i‖² - ‖m - i‖² = 4 · Im m ≥ 0`.) The forward direction
of the Herglotz ⟷ Schur correspondence — the carrier's disk picture. -/
theorem cayley_herglotz_schur (m : ℂ) (hm : 0 ≤ m.im) (h : m + Complex.I ≠ 0) :
    ‖(m - Complex.I) / (m + Complex.I)‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr h)]
  have key : ‖m - Complex.I‖ ^ 2 ≤ ‖m + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
               Complex.I_re, Complex.I_im]
    nlinarith [hm]
  nlinarith [norm_nonneg (m - Complex.I), norm_nonneg (m + Complex.I), key]

/-- **Cayley inverse: Schur ⟹ Herglotz.** If `‖θ‖ ≤ 1` (a Schur value, `θ ≠ 1`), the inverse Cayley
transform `i(1+θ)/(1-θ)` has nonnegative imaginary part — a Herglotz value
(`Im(i(1+θ)/(1-θ)) = (1 - ‖θ‖²)/‖1-θ‖² ≥ 0`). With `cayley_herglotz_schur` this is the full
Herglotz ⟷ Schur correspondence (both directions), the carrier's two-picture equivalence. -/
theorem cayley_schur_herglotz (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (h : θ ≠ 1) :
    0 ≤ (Complex.I * ((1 + θ) / (1 - θ))).im := by
  have hden : 0 < Complex.normSq (1 - θ) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul, zero_add, Complex.div_re,
      ← add_div]
  apply div_nonneg _ (le_of_lt hden)
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
             Complex.sub_im]
  nlinarith [Complex.sq_norm θ, Complex.normSq_apply θ, hθ, norm_nonneg θ]

/-- **The Blaschke factor is Schur.** For `‖a‖ ≤ 1`, `‖z‖ ≤ 1`, the Blaschke factor
`b_a(z) = (z - a)/(1 - conj a · z)` satisfies `‖b_a(z)‖ ≤ 1`
(`‖1-āz‖² - ‖z-a‖² = (1-‖a‖²)(1-‖z‖²) ≥ 0`). The Blaschke factor is the disk-picture building block
of the Krein–Langer `N_κ` negative squares — one factor per `ℂ⁺` pole, the disk analog of an off-line
carrier pole. -/
theorem blaschke_schur (a z : ℂ) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (h : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    ‖(z - a) / (1 - (starRingEnd ℂ) a * z)‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr h)]
  have hA : (0 : ℝ) ≤ 1 - (a.re ^ 2 + a.im ^ 2) := by
    nlinarith [Complex.sq_norm a, Complex.normSq_apply a, ha, norm_nonneg a]
  have hZ : (0 : ℝ) ≤ 1 - (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [Complex.sq_norm z, Complex.normSq_apply z, hz, norm_nonneg z]
  have key : ‖z - a‖ ^ 2 ≤ ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
               Complex.one_im, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_nonneg hA hZ]
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z), key]

/-- **A finite Blaschke product is Schur (the κ₋ factor).** A product of Blaschke factors over poles
`a : Fin n → ℂ` (each `‖a i‖ ≤ 1`) satisfies `‖∏ b_{a_i}(z)‖ ≤ 1` for `‖z‖ ≤ 1`. This finite Blaschke
product is the disk-picture realization of the Krein–Langer `N_κ` factor (degree = κ₋ = number of
`ℂ⁺` carrier poles); it is the building block of the Krein–Langer factorization `m = B · m₀`. -/
theorem finite_blaschke_schur {n : ℕ} (a : Fin n → ℂ) (z : ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hz : ‖z‖ ≤ 1) (h : ∀ i, 1 - (starRingEnd ℂ) (a i) * z ≠ 0) :
    ‖∏ i, (z - a i) / (1 - (starRingEnd ℂ) (a i) * z)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i _; exact norm_nonneg _
  · intro i _; exact blaschke_schur (a i) z (ha i) hz (h i)

/-- **Finite Szegő / de Branges reproducing kernel is PSD.** For nodes `w : Fin m → ℂ`, the degree-`N`
truncated Szegő kernel `S_N(w_j,w_k) = ∑_{n<N} w_j^n · conj(w_k^n)` is positive semidefinite — a
Finset sum of rank-1 Gram matrices `v_n v_nᴴ` (`v_n = (w_j^n)_j`). This is the polynomial
reproducing-kernel positivity underlying the disk-side de Branges spaces (the `N→∞` limit is the
Szegő kernel `1/(1 - conj(w_k) w_j)`). -/
theorem szego_truncation_posSemidef {m : ℕ} (N : ℕ) (w : Fin m → ℂ) :
    (Matrix.of (fun j k => ∑ n ∈ Finset.range N, (w j) ^ n * star ((w k) ^ n))).PosSemidef := by
  have hterm : ∀ n, (Matrix.of (fun j k : Fin m => (w j) ^ n * star ((w k) ^ n))).PosSemidef := by
    intro n
    have hBB : (Matrix.of (fun j k : Fin m => (w j) ^ n * star ((w k) ^ n)))
        = (Matrix.of (fun (j : Fin m) (_ : Fin 1) => (w j) ^ n))
          * (Matrix.of (fun (j : Fin m) (_ : Fin 1) => (w j) ^ n))ᴴ := by
      ext j k
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [hBB]; exact Matrix.posSemidef_self_mul_conjTranspose _
  have hsum : (Matrix.of (fun j k => ∑ n ∈ Finset.range N, (w j) ^ n * star ((w k) ^ n)))
      = ∑ n ∈ Finset.range N, Matrix.of (fun j k : Fin m => (w j) ^ n * star ((w k) ^ n)) := by
    ext j k; simp [Matrix.sum_apply, Matrix.of_apply]
  rw [hsum]
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero
    (fun n _ => hterm n)

/-- **Forward Krein–Langer factorization (Schur picture): a Blaschke·Schur product is Schur.**
If `B = ∏ b_{a_i}` is a finite Blaschke product (each `‖a i‖ ≤ 1`) and `θ₀` is Schur (`‖θ₀‖ ≤ 1`),
then the factored form `B(z)·θ₀` satisfies `‖B(z)·θ₀‖ ≤ 1` — it is Schur. This is the forward
direction of the Krein–Langer factorization `m = B · m₀` (disk picture `θ = B · θ₀`): the factored
form lands in the Schur class. (The converse — every Schur `θ` factors this way with `deg B = κ₋` —
is the de Branges realization theorem, the open converse.) -/
theorem kreinLanger_factored_schur {n : ℕ} (a : Fin n → ℂ) (θ₀ z : ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hz : ‖z‖ ≤ 1) (h : ∀ i, 1 - (starRingEnd ℂ) (a i) * z ≠ 0)
    (hθ : ‖θ₀‖ ≤ 1) :
    ‖(∏ i, (z - a i) / (1 - (starRingEnd ℂ) (a i) * z)) * θ₀‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (finite_blaschke_schur a z ha hz h) (norm_nonneg _) hθ

/-- **de Branges–Rovnyak diagonal positivity.** For a Schur value `θ` (`‖θ‖ ≤ 1`) and `w` in the open
disk (`‖w‖ < 1`), the diagonal of the de Branges–Rovnyak kernel `K_θ(w,w) = (1 - ‖θ‖²)/(1 - ‖w‖²)`
is nonnegative — the defining positivity of the model space `H(θ)`. -/
theorem deBrangesRovnyak_diag_nonneg (θ w : ℂ) (hθ : ‖θ‖ ≤ 1) (hw : ‖w‖ < 1) :
    0 ≤ (1 - ‖θ‖ ^ 2) / (1 - ‖w‖ ^ 2) := by
  apply div_nonneg
  · nlinarith [norm_nonneg θ, hθ]
  · nlinarith [norm_nonneg w, hw]

/-- **The Cayley transform maps the upper half-plane into the open unit disk.** For `Im z > 0`,
`‖(z - i)/(z + i)‖ < 1`. The conformal equivalence `ℂ⁺ ≅ 𝔻` underlying the entire Herglotz ⟷ Schur
correspondence (`cayley_herglotz_schur` is its boundary `≤` version). -/
theorem cayley_upperHalfPlane_to_disk (z : ℂ) (hz : 0 < z.im) :
    ‖(z - Complex.I) / (z + Complex.I)‖ < 1 := by
  have h : z + Complex.I ≠ 0 := by
    intro hc
    have him : (z + Complex.I).im = 0 := by rw [hc]; rfl
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h)]
  have key : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
               Complex.I_re, Complex.I_im]
    nlinarith [hz]
  nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I), key]

/-- **Schur-product (Hadamard) closure of de Branges reproducing kernels.** The entrywise product of
two Szegő/de Branges reproducing kernels is again positive semidefinite (Schur product theorem) — a
weighted/Bergman-type reproducing kernel. This closure builds de Branges spaces with products/weights
from the basic Szegő kernel. -/
theorem szego_hadamard_posSemidef {m : ℕ} (N M : ℕ) (w : Fin m → ℂ) :
    ((Matrix.of (fun j k => ∑ n ∈ Finset.range N, (w j) ^ n * star ((w k) ^ n))).hadamard
      (Matrix.of (fun j k => ∑ n ∈ Finset.range M, (w j) ^ n * star ((w k) ^ n)))).PosSemidef :=
  (szego_truncation_posSemidef N w).hadamard (szego_truncation_posSemidef M w)

end

end GaloisForLFunctions
