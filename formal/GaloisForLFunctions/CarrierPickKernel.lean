import GaloisForLFunctions.Core

/-!
# The carrier Pick kernel: finite real-spectrum positivity and pole witnesses

The Weyl-function / carrier program (`dss-multiplicity-estimate-spectral-genericity.md` §6): the
finite carrier is `m(z) = Σ_i 1/(t_i - z)` (the finite shadow of `-Ξ'/Ξ` for a spectral carrier),
with **Pick kernel**
`K(z,w) = (m(z) - conj(m(w)))/(z - conj(w))`, and `RH ⟺ all t_ρ real ⟺ m ∈ N₀ (Herglotz) ⟺ K ⪰ 0`.

This file formalizes finite, elementary carrier fragments. It proves the real-spectrum Gram/PSD
direction, explicit single-pole and FE-conjugate-pair witnesses that break Herglotz/Pick positivity,
and the FE conjugate-pair equivalence `Herglotz on ℂ⁺ ↔ pole on the real line`. The infinite carrier
`m_ξ`, full multi-pole inertia, pole reconstruction, DSS, and RH remain outside this file.

* `pick_kernel_posSemidef` — the resolvent Gram `Σ_i ν_i(z_j) conj(ν_i(z_k))`, `ν_i(z)=(t_i-z)⁻¹`,
  is positive semidefinite (it is `B Bᴴ`), for any finite real node set.
* `pick_gram_eq_kernel` — for **real** nodes that Gram **equals** the carrier's Pick kernel
  `(m(z) - conj(m(w)))/(z - conj(w))`, `m(z)=Σ_i (t_i-z)⁻¹`.

Together: for finite carriers, the real/on-line case is a manifest positive Gram/Herglotz object, and
upper-half-plane poles give explicit negative one-point tests.
-/

open scoped BigOperators ComplexOrder

open Matrix

namespace GaloisForLFunctions

noncomputable section

/-- **Real spectrum ⟹ Pick kernel PSD (Gram form).** For a finite real node set `t : Fin n → ℝ`
and evaluation points `z : Fin m → ℂ`, the resolvent-Gram matrix
`K_{jk} = Σ_i (t_i - z_j)⁻¹ · conj((t_i - z_k)⁻¹)` is positive semidefinite — it is `B Bᴴ` with
`B_{j,i} = (t_i - z_j)⁻¹`. The manifest-positivity (easy) half of `K_ξ ⪰ 0 ⟺ RH`. -/
theorem pick_kernel_posSemidef {n m : ℕ} (t : Fin n → ℝ) (z : Fin m → ℂ) :
    (Matrix.of (fun j k => ∑ i, ((t i : ℂ) - z j)⁻¹ * star (((t i : ℂ) - z k)⁻¹))).PosSemidef := by
  let B : Matrix (Fin m) (Fin n) ℂ := Matrix.of (fun j i => ((t i : ℂ) - z j)⁻¹)
  have hBB : (Matrix.of (fun j k => ∑ i, ((t i : ℂ) - z j)⁻¹ * star (((t i : ℂ) - z k)⁻¹)))
      = B * Bᴴ := by
    ext j k
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, B, Matrix.of_apply]
  rw [hBB]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- **For a real spectrum, the resolvent Gram equals the carrier's Pick kernel.**
With `m(z) = Σ_i (t_i - z)⁻¹` and real nodes `t`, the Gram `Σ_i (t_i-z)⁻¹ conj((t_i-w)⁻¹)` equals
`(m(z) - conj(m(w)))/(z - conj(w))` — so `pick_kernel_posSemidef` is the Pick kernel of `m` for a real
spectrum. (Nodes assumed away from `z, w` and `z ≠ conj(w)`.) -/
theorem pick_gram_eq_kernel {n : ℕ} (t : Fin n → ℝ) (z w : ℂ)
    (hz : ∀ i, ((t i : ℂ) - z) ≠ 0) (hw : ∀ i, ((t i : ℂ) - w) ≠ 0) (hzw : z - star w ≠ 0) :
    (∑ i, ((t i : ℂ) - z)⁻¹ * star (((t i : ℂ) - w)⁻¹))
      = ((∑ i, ((t i : ℂ) - z)⁻¹) - star (∑ i, ((t i : ℂ) - w)⁻¹)) / (z - star w) := by
  rw [star_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ht : star ((t i : ℂ)) = (t i : ℂ) := Complex.conj_ofReal _
  have hsw : star ((t i : ℂ) - w) = (t i : ℂ) - star w := by rw [star_sub, ht]
  have hsw0 : ((t i : ℂ) - star w) ≠ 0 := by rw [← hsw]; exact star_ne_zero.mpr (hw i)
  rw [star_inv₀, hsw]
  field_simp [hz i, hsw0, hzw]
  ring

/-- **Real spectrum ⟹ carrier Herglotz (forward, function level).** For a finite real spectrum
`t : Fin n → ℝ`, the carrier `m(z) = Σ_i (t_i - z)⁻¹` has `Im m(z) ≥ 0` for every `z ∈ ℂ⁺` — it is a
Nevanlinna (Herglotz) function. The carrier-level RH shadow, forward direction (each term
`Im((t_i - z)⁻¹) = Im(z)/|t_i - z|² ≥ 0`). -/
theorem real_spectrum_carrier_herglotz {n : ℕ} (t : Fin n → ℝ) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (∑ i, ((t i : ℂ) - z)⁻¹).im := by
  rw [Complex.im_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.inv_im]
  have him : ((t i : ℂ) - z).im = -z.im := by simp [Complex.sub_im, Complex.ofReal_im]
  rw [him]
  apply div_nonneg
  · linarith
  · exact Complex.normSq_nonneg _

/-- **No pole in `ℂ⁺` ⟹ carrier Herglotz (general forward).** If every pole has `Im tᵢ ≤ 0` (none in
the open upper half-plane), the carrier `m(z) = Σ_i (tᵢ - z)⁻¹` satisfies `Im m(z) ≥ 0` on `ℂ⁺`.
Generalizes `real_spectrum_carrier_herglotz` (the `Im tᵢ = 0` case). With `conj_pair_not_herglotz`
(converse, FE conjugate-pair) this is the carrier dichotomy: Herglotz ⟺ no `ℂ⁺` pole. -/
theorem poles_lower_carrier_herglotz {n : ℕ} (t : Fin n → ℂ) (hpoles : ∀ i, (t i).im ≤ 0)
    (z : ℂ) (hz : 0 < z.im) : 0 ≤ (∑ i, (t i - z)⁻¹).im := by
  rw [Complex.im_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.inv_im, Complex.sub_im]
  apply div_nonneg
  · have := hpoles i; linarith
  · exact Complex.normSq_nonneg _

/-- **The `κ₋` mechanism (converse direction, single pole): a pole in the open upper half-plane breaks
Herglotz.** If the carrier `m(z) = (t - z)⁻¹` has its pole `t` in `ℂ⁺` (`Im t > 0`), then there is
`z ∈ ℂ⁺` with `Im(m(z)) < 0` — so `m` is not Nevanlinna and (one-dimensionally) the Pick kernel is not
PSD. This is the finite shadow of "off-line zero ⟹ carrier not Herglotz ⟹ not RH": the `κ₋ > 0`
side, proved (not deferred). Witness `z = t - i·(Im t)/2`. -/
theorem pole_upper_not_herglotz (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧ ((t - z)⁻¹).im < 0 := by
  refine ⟨t - Complex.I * ((t.im / 2 : ℝ) : ℂ), ?_, ?_⟩
  · simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
          Complex.ofReal_re]
    linarith
  · have hsub : t - (t - Complex.I * ((t.im / 2 : ℝ) : ℂ)) = Complex.I * ((t.im / 2 : ℝ) : ℂ) := by
      ring
    rw [hsub, Complex.inv_im]
    have him : (Complex.I * ((t.im / 2 : ℝ) : ℂ)).im = t.im / 2 := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have hns : Complex.normSq (Complex.I * ((t.im / 2 : ℝ) : ℂ)) = (t.im / 2) * (t.im / 2) := by
      simp [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]; ring
    rw [him, hns]
    exact div_neg_of_neg_of_pos (by linarith) (mul_pos (by linarith) (by linarith))

/-- A `1×1` complex matrix with strictly-negative-real-part entry is not positive semidefinite
(its diagonal entry is not `≥ 0` in the complex star-order). -/
theorem oneByOne_not_posSemidef (c : ℂ) (hc : c.re < 0) :
    ¬ (Matrix.of (fun (_ _ : Fin 1) => c)).PosSemidef := by
  intro h
  have hd := h.diag_nonneg (i := 0)
  simp only [Matrix.of_apply] at hd
  rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hd
  linarith [hd.1]

/-- **Single-pole finite Krein–Langer (converse, matrix level): a pole in `ℂ⁺` ⟹ Pick matrix not PSD.**
For the carrier `m(z) = (t - z)⁻¹` with `Im t > 0`, there is a witness `z ∈ ℂ⁺` at which the `1×1` Pick
matrix `[ (m(z) - conj(m(z)))/(z - conj(z)) ]` is **not** positive semidefinite. With
`pick_kernel_posSemidef` (real spectrum ⟹ PSD) this gives the single-pole characterization in both
directions: `κ₋ = 0` (no `ℂ⁺` pole) ⟺ Pick PSD. -/
theorem single_pole_pick_not_posSemidef (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧
      ¬ (Matrix.of (fun (_ _ : Fin 1) =>
          ((t - z)⁻¹ - star ((t - z)⁻¹)) / (z - star z))).PosSemidef := by
  obtain ⟨z, hz, hm⟩ := pole_upper_not_herglotz t ht
  refine ⟨z, hz, oneByOne_not_posSemidef _ ?_⟩
  have hzc : z - star z = ((2 * z.im : ℝ) : ℂ) * Complex.I := by
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.sub_conj]
  have hac : (t - z)⁻¹ - star ((t - z)⁻¹) = ((2 * ((t - z)⁻¹).im : ℝ) : ℂ) * Complex.I := by
    rw [show star ((t - z)⁻¹) = (starRingEnd ℂ) ((t - z)⁻¹) from rfl, Complex.sub_conj]
  rw [hac, hzc, mul_div_mul_right _ _ Complex.I_ne_zero,
      show (((2 * ((t - z)⁻¹).im : ℝ)) : ℂ) / ((2 * z.im : ℝ) : ℂ)
        = (((2 * ((t - z)⁻¹).im) / (2 * z.im) : ℝ) : ℂ) from by push_cast; ring,
      Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- `Im (I·c)⁻¹ = -1/c` for a nonzero real `c`. -/
lemma imInv_I_mul (c : ℝ) (hc : c ≠ 0) : (Complex.I * (c : ℂ))⁻¹.im = -1 / c := by
  rw [Complex.inv_im]
  have him : (Complex.I * (c : ℂ)).im = c := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hns : Complex.normSq (Complex.I * (c : ℂ)) = c * c := by
    simp [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
  rw [him, hns]; field_simp

/-- **Conjugate-pair carrier with a `ℂ⁺` pole is not Herglotz** (the functional-equation symmetry case
— the actual `ξ` structure). For `m(z) = (t - z)⁻¹ + (conj t - z)⁻¹` (a conjugate pair of poles, i.e.
an off-line zero pair) with `Im t > 0`, there is `z ∈ ℂ⁺` with `Im m(z) < 0`: the `κ₋ > 0` mechanism
for the FE-symmetric carrier. Witness `z = t - i·Im(t)/2`, giving `Im m(z) = -4/(3 Im t) < 0`. With
`real_spectrum_carrier_herglotz` (forward): the FE-symmetric carrier is Herglotz ⟺ it has no
conjugate-pair (off-line) pole. -/
theorem conj_pair_not_herglotz (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧ ((t - z)⁻¹ + (star t - z)⁻¹).im < 0 := by
  refine ⟨t - Complex.I * ((t.im / 2 : ℝ) : ℂ), ?_, ?_⟩
  · simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
          Complex.ofReal_re]
    linarith
  · rw [Complex.add_im]
    have e1 : t - (t - Complex.I * ((t.im / 2 : ℝ) : ℂ)) = Complex.I * ((t.im / 2 : ℝ) : ℂ) := by ring
    have hsc : t - star t = ((2 * t.im : ℝ) : ℂ) * Complex.I := by
      rw [show star t = (starRingEnd ℂ) t from rfl, Complex.sub_conj]
    have e2 : star t - (t - Complex.I * ((t.im / 2 : ℝ) : ℂ))
        = Complex.I * (((-3 * t.im / 2 : ℝ)) : ℂ) := by
      have hst : star t - t = -(((2 * t.im : ℝ) : ℂ) * Complex.I) := by rw [← hsc]; ring
      rw [show star t - (t - Complex.I * ((t.im / 2 : ℝ) : ℂ))
            = (star t - t) + Complex.I * ((t.im / 2 : ℝ) : ℂ) from by ring, hst]
      push_cast; ring
    rw [e1, e2, imInv_I_mul _ (by positivity), imInv_I_mul _ (by intro h; nlinarith [ht])]
    have hgoal : -1 / (t.im / 2) + -1 / (-3 * t.im / 2) = -4 / (3 * t.im) := by
      field_simp; ring
    rw [hgoal]
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- The Pick diagonal value `(m - conj m)/(z - conj z) = Im(m)/Im(z)` (real). -/
lemma pickDiag_eq (m z : ℂ) (hz : z.im ≠ 0) :
    (m - star m) / (z - star z) = ((m.im / z.im : ℝ) : ℂ) := by
  have hm : m - star m = ((2 * m.im : ℝ) : ℂ) * Complex.I := by
    rw [show star m = (starRingEnd ℂ) m from rfl, Complex.sub_conj]
  have hzz : z - star z = ((2 * z.im : ℝ) : ℂ) * Complex.I := by
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.sub_conj]
  rw [hm, hzz, mul_div_mul_right _ _ Complex.I_ne_zero]
  rw [show ((2 * m.im : ℝ) : ℂ) / ((2 * z.im : ℝ) : ℂ) = ((m.im / z.im : ℝ) : ℂ) from by
    push_cast; field_simp]

/-- The real part of the Pick diagonal is `Im(m)/Im(z)`. -/
lemma pickDiag_re (m z : ℂ) (hz : z.im ≠ 0) :
    ((m - star m) / (z - star z)).re = m.im / z.im := by
  rw [pickDiag_eq m z hz, Complex.ofReal_re]

/-- **Conjugate-pair carrier with a `ℂ⁺` pole: Pick matrix not PSD (matrix-level converse, `κ₋ ≥ 1`).**
The off-line conjugate-pair carrier (the FE structure) yields, at the witness `z ∈ ℂ⁺`, a `1×1` Pick
matrix that is not positive semidefinite — so its negative inertia `κ₋ ≥ 1`. Lifts
`conj_pair_not_herglotz` to the matrix level via `pickDiag_re`. -/
theorem conj_pair_pick_not_posSemidef (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧
      ¬ (Matrix.of (fun (_ _ : Fin 1) =>
          (((t - z)⁻¹ + (star t - z)⁻¹) - star ((t - z)⁻¹ + (star t - z)⁻¹))
            / (z - star z))).PosSemidef := by
  obtain ⟨z, hz, hm⟩ := conj_pair_not_herglotz t ht
  refine ⟨z, hz, oneByOne_not_posSemidef _ ?_⟩
  rw [pickDiag_re _ z hz.ne']
  exact div_neg_of_neg_of_pos hm hz

/-- **Carrier dichotomy as an equivalence (FE conjugate pair): Herglotz ⟺ on-line.**
The conjugate-pair carrier `m(z) = (t - z)⁻¹ + (conj t - z)⁻¹` is Herglotz on `ℂ⁺` (`Im m ≥ 0`)
**iff** `t` is real (`Im t = 0`) — i.e. the conjugate zero-pair lies on the critical line. This is
RH's finite carrier-shadow as a genuine `⟺`: an off-line pair (`Im t ≠ 0`) ⟺ the carrier fails
Herglotz. Combines `conj_pair_not_herglotz` (both signs, via `star_star`) and the real-pole forward. -/
theorem conj_pair_herglotz_iff (t : ℂ) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ ((t - z)⁻¹ + (star t - z)⁻¹).im) ↔ t.im = 0 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstim : 0 < (star t).im := by
        rw [show star t = (starRingEnd ℂ) t from rfl, Complex.conj_im]; linarith
      obtain ⟨z, hz, hm⟩ := conj_pair_not_herglotz (star t) hstim
      rw [star_star] at hm
      have hh := h z hz
      rw [add_comm] at hh
      linarith
    · obtain ⟨z, hz, hm⟩ := conj_pair_not_herglotz t hgt
      linarith [h z hz]
  · intro h z hz
    have hst : star t = t := by
      apply Complex.ext
      · rw [show star t = (starRingEnd ℂ) t from rfl, Complex.conj_re]
      · rw [show star t = (starRingEnd ℂ) t from rfl, Complex.conj_im, h]; ring
    rw [Complex.add_im, hst]
    have hterm : 0 ≤ ((t - z)⁻¹).im := by
      rw [Complex.inv_im]
      apply div_nonneg
      · rw [Complex.sub_im, h]; simp; linarith
      · exact Complex.normSq_nonneg _
    linarith

/-- Positive witness: the off-line conjugate-pair carrier has `Im m(z) > 0` at `z = t + i·Im t`
(`Im m = 4/(3 Im t) > 0`). -/
theorem conj_pair_carrier_pos (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧ 0 < ((t - z)⁻¹ + (star t - z)⁻¹).im := by
  refine ⟨t + Complex.I * ((t.im : ℝ) : ℂ), ?_, ?_⟩
  · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
          Complex.ofReal_re]
    linarith
  · rw [Complex.add_im]
    have e1 : t - (t + Complex.I * ((t.im : ℝ) : ℂ)) = Complex.I * (((-t.im : ℝ)) : ℂ) := by
      push_cast; ring
    have hsc : t - star t = ((2 * t.im : ℝ) : ℂ) * Complex.I := by
      rw [show star t = (starRingEnd ℂ) t from rfl, Complex.sub_conj]
    have e2 : star t - (t + Complex.I * ((t.im : ℝ) : ℂ)) = Complex.I * (((-3 * t.im : ℝ)) : ℂ) := by
      have hst : star t - t = -(((2 * t.im : ℝ) : ℂ) * Complex.I) := by rw [← hsc]; ring
      rw [show star t - (t + Complex.I * ((t.im : ℝ) : ℂ))
            = (star t - t) - Complex.I * ((t.im : ℝ) : ℂ) from by ring, hst]
      push_cast; ring
    rw [e1, e2, imInv_I_mul _ (by intro h; nlinarith [ht]), imInv_I_mul _ (by intro h; nlinarith [ht])]
    have hgoal : -1 / (-t.im) + -1 / (-3 * t.im) = 4 / (3 * t.im) := by field_simp; ring
    rw [hgoal]
    positivity

/-- **Off-line conjugate pair ⟹ carrier indefinite on `ℂ⁺` (qualitative Krein–Langer).**
The carrier of an off-line conjugate pair (`Im t > 0`) takes **both** signs of `Im m` on `ℂ⁺`, so its
Pick matrix has a positive direction and a negative direction (`n₊ ≥ 1 ∧ n₋ ≥ 1`) — the qualitative
inertia picture of an off-line pole (exact count `κ₋ = 1` needs the Loewner-rank bound, Stage 1). -/
theorem conj_pair_carrier_indefinite (t : ℂ) (ht : 0 < t.im) :
    (∃ z : ℂ, 0 < z.im ∧ 0 < ((t - z)⁻¹ + (star t - z)⁻¹).im) ∧
    (∃ z : ℂ, 0 < z.im ∧ ((t - z)⁻¹ + (star t - z)⁻¹).im < 0) :=
  ⟨conj_pair_carrier_pos t ht, conj_pair_not_herglotz t ht⟩

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **Single-pole Pick lower witness, vector form.** If a carrier has one pole in `ℂ⁺`, then at an
upper-half-plane test point its `1×1` Pick matrix has an explicit nonzero vector with negative
Hermitian quadratic value. This strengthens the earlier `not PosSemidef` witness into the vector
language used by the Stage-1 inertia ledger. -/
theorem single_pole_pick_negative_vector (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧ ∃ x : Fin 1 → ℂ, x ≠ 0 ∧
      (star x ⬝ᵥ (Matrix.of (fun (_ _ : Fin 1) =>
          ((t - z)⁻¹ - star ((t - z)⁻¹)) / (z - star z))).mulVec x).re < 0 := by
  obtain ⟨z, hz, hm⟩ := pole_upper_not_herglotz t ht
  refine ⟨z, hz, fun _ => 1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    norm_num at h0
  · have hc : (((t - z)⁻¹ - star ((t - z)⁻¹)) / (z - star z)).re < 0 := by
      rw [pickDiag_re _ z hz.ne']
      exact div_neg_of_neg_of_pos hm hz
    simpa [Matrix.mulVec, dotProduct] using hc

/-- **FE conjugate-pair Pick lower witness, vector form.** An off-line conjugate pole pair gives an
upper-half-plane test point and an explicit nonzero vector on which the corresponding `1×1` Pick
matrix is negative. This is still the one-point `κ₋ ≥ 1` lower witness, not the multi-node
`κ₋ ≥ #{off-line poles}` theorem. -/
theorem conj_pair_pick_negative_vector (t : ℂ) (ht : 0 < t.im) :
    ∃ z : ℂ, 0 < z.im ∧ ∃ x : Fin 1 → ℂ, x ≠ 0 ∧
      (star x ⬝ᵥ (Matrix.of (fun (_ _ : Fin 1) =>
          (((t - z)⁻¹ + (star t - z)⁻¹) - star ((t - z)⁻¹ + (star t - z)⁻¹))
            / (z - star z))).mulVec x).re < 0 := by
  obtain ⟨z, hz, hm⟩ := conj_pair_not_herglotz t ht
  refine ⟨z, hz, fun _ => 1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    norm_num at h0
  · have hc :
        ((((t - z)⁻¹ + (star t - z)⁻¹) - star ((t - z)⁻¹ + (star t - z)⁻¹))
            / (z - star z)).re < 0 := by
      rw [pickDiag_re _ z hz.ne']
      exact div_neg_of_neg_of_pos hm hz
    simpa [Matrix.mulVec, dotProduct] using hc

end

end GaloisForLFunctions
