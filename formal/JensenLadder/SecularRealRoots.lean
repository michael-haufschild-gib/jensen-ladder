import Mathlib

/-!
# Positive secular weights ⟹ real secular spectrum (the finite Lee–Yang core)

For the CCM secular equation `f(z) = ∑_i u_i/(d_i − z) = 1` (dyson's reconstruction `D′ = diag(d) − u 1ᵀ`,
`SecularReconstruction`), with a **real grid** `d_i ∈ ℝ` and **non-negative real weights** `u_i ≥ 0`
(not all zero), every solution of `f(z)=1` is **real**: off the real axis `f` has nonzero imaginary part,
so it cannot equal the real value `1`.

This is the finite, RH-free backbone of the Herglotz reduction
(`docs/rh/hawking_eta_secular_sigma1_forcing_20260618.md`,
`docs/rh/hawking_secular_weight_positivity_20260618.md`): *one-signed real weights ⟹ Herglotz transform ⟹
real spectrum* (the converse is false — signed weights can still give real roots — so only this direction is
a theorem). It is a finite **Lee–Yang**-type statement: positive (ferromagnetic) residues localize the roots
on the real axis, with the zeros never used as input.

Key identity: `Im f(z) = (Im z)·∑_i u_i/‖d_i − z‖²`, which is sign(Im z)·(positive) when some `u_i>0`.

Companion `secular_strictMono`: with the same positive residues, the *real* secular function is strictly
increasing on any pole-free interval — the **interlacing engine** (one root of `f=1` per gap), i.e. the
formal *density* statement (the secular spectrum carries the grid's counting function). Together: positive
residues ⟹ a real spectrum interlacing the grid.
-/

open Finset

namespace JensenLadder

/-- **Positive secular weights ⟹ real spectrum (finite Lee–Yang).** With a real grid `d`, non-negative
real weights `u` (some strictly positive), and `z` off the real axis (none of the `d_i` equal to `z`), the
secular transform `∑_i u_i/(d_i − z)` cannot equal `1`. Hence every root of the secular equation is real. -/
theorem secular_roots_real {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hpos : ∃ i, 0 < u i)
    (z : ℂ) (hz : z.im ≠ 0) (hd : ∀ i, ((d i : ℂ) - z) ≠ 0) :
    (∑ i, (u i : ℂ) / ((d i : ℂ) - z)) ≠ 1 := by
  have hterm : ∀ i, ((u i : ℂ) / ((d i : ℂ) - z)).im
      = z.im * (u i / Complex.normSq ((d i : ℂ) - z)) := by
    intro i
    rw [Complex.div_im]
    simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, Complex.sub_re,
      Complex.ofReal_im, zero_mul, zero_sub]
    field_simp
    ring
  have hsum_im : (∑ i, (u i : ℂ) / ((d i : ℂ) - z)).im
      = z.im * ∑ i, u i / Complex.normSq ((d i : ℂ) - z) := by
    rw [Complex.im_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hSpos : 0 < ∑ i, u i / Complex.normSq ((d i : ℂ) - z) := by
    obtain ⟨j, hj⟩ := hpos
    apply Finset.sum_pos'
    · intro i _
      exact div_nonneg (hu i) (le_of_lt (Complex.normSq_pos.mpr (hd i)))
    · exact ⟨j, mem_univ j, div_pos hj (Complex.normSq_pos.mpr (hd j))⟩
  intro h
  have him0 : (∑ i, (u i : ℂ) / ((d i : ℂ) - z)).im = 0 := by rw [h]; simp
  rw [hsum_im] at him0
  exact (mul_ne_zero hz (ne_of_gt hSpos)) him0

/-- **Strict monotonicity between poles (interlacing engine).** With non-negative residues `u` (some
positive), the real secular function `x ↦ ∑_i u_i/(d_i − x)` is strictly increasing on any interval
`(x,y)` containing no pole `d_i` (`d_i < x` or `y < d_i` for every `i`). Combined with `f → −∞` at the
left pole and `f → +∞` at the right pole of a gap, this forces **exactly one root of `f = 1` per gap**
(the roots interlace the grid) — the formal density statement: the secular spectrum has the grid's
counting function. -/
theorem secular_strictMono {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hpos : ∃ i, 0 < u i)
    {x y : ℝ} (hxy : x < y) (hgap : ∀ i, d i < x ∨ y < d i) :
    (∑ i, u i / (d i - x)) < (∑ i, u i / (d i - y)) := by
  have hden : ∀ i, 0 < (d i - y) * (d i - x) := by
    intro i
    rcases hgap i with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hdx : ∀ i, d i - x ≠ 0 := by
    intro i; rcases hgap i with h | h
    · exact ne_of_lt (by linarith)
    · exact ne_of_gt (by linarith)
  have hdy : ∀ i, d i - y ≠ 0 := by
    intro i; rcases hgap i with h | h
    · exact ne_of_lt (by linarith)
    · exact ne_of_gt (by linarith)
  rw [← sub_pos, ← Finset.sum_sub_distrib]
  have hterm : ∀ i, u i / (d i - y) - u i / (d i - x)
      = u i * (y - x) / ((d i - y) * (d i - x)) := by
    intro i
    rw [div_sub_div (u i) (u i) (hdy i) (hdx i)]
    congr 1
    ring
  obtain ⟨j, hj⟩ := hpos
  apply Finset.sum_pos'
  · intro i _
    rw [hterm i]
    exact div_nonneg (mul_nonneg (hu i) (by linarith)) (le_of_lt (hden i))
  · exact ⟨j, mem_univ j, by rw [hterm j]; exact div_pos (mul_pos hj (by linarith)) (hden j)⟩

end JensenLadder
