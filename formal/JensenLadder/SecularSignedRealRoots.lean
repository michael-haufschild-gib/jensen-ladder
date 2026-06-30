/-
# Signed-residue secular real-rootedness — the exact (quadratic/Herglotz) condition

Author: berry, 2026-06-18. Program: `program_T3_T5_self_product_construction`.

`SecularRealRoots.secular_roots_real` proves: **non-negative** weights `u_i ≥ 0` ⟹ the secular equation
`∑ u_i/(d_i − z) = 1` has only real roots (finite Lee–Yang). But the actual CCM secular residues are **signed**
(the ground state `u` oscillates in sign), so that theorem does not apply to the arithmetic case, and its
docstring notes the converse fails.

This file gives the **per-point** no-root criterion, valid for residues of **any sign**:
at an off-axis `z`, `z` fails to be a root as soon as the **inverse-square-weighted residue field**
`Φ(z) = ∑_i r_i / ‖d_i − z‖²` is positive there (`Im (∑ r_i/(d_i−z)) = Im(z)·Φ(z)`).

**Honest scope (a corrected setback).** The *global* condition "`Φ>0` for every off-axis `z`" is **NOT** weaker
than pointwise `r_i ≥ 0`; it is **equivalent** to it: if some `r_j < 0` then near `z = d_j + iε` the term
`r_j/ε² → −∞` dominates, so `Φ(z) < 0` (verified numerically). Globally this reproduces Lee–Yang, not a
generalization. The genuine new content is **LOCALIZATION**: complex secular roots are confined to
`{z : Φ(z) ≤ 0}`, a neighborhood of the **negative-residue poles** (the ground state's sign-oscillations).
Hence **RH ⟺ no secular root in `{Φ ≤ 0}`** — RH-violation, if any, lives only near the negative residues.
This is still the quadratic/Herglotz (spectral-identification) piece, not a linear/unitary invariant (cf.
`berry_hp_cayley_falsification_20260618`); it isolates/localizes the wall, it does not cross it.
-/
import Mathlib

open Finset

namespace JensenLadder

/-- **Signed-residue secular real-rootedness (sharpened Lee–Yang).** For real grid `d`, residues `r` of
ANY sign, and `z` off the real axis: if the inverse-square-weighted residue field
`∑ r_i / ‖d_i − z‖²` is positive at `z`, then `∑ r_i/(d_i − z) ≠ 1`. Hence the secular spectrum has no complex
point wherever this field is positive — the exact condition (the pointwise `r_i ≥ 0` of the positive case is
sufficient but not necessary). -/
theorem secular_roots_real_signed {n : ℕ} (d : Fin n → ℝ) (r : Fin n → ℝ)
    (z : ℂ) (hz : z.im ≠ 0)
    (hpos : 0 < ∑ i, r i / Complex.normSq ((d i : ℂ) - z)) :
    (∑ i, (r i : ℂ) / ((d i : ℂ) - z)) ≠ 1 := by
  have hterm : ∀ i, ((r i : ℂ) / ((d i : ℂ) - z)).im
      = z.im * (r i / Complex.normSq ((d i : ℂ) - z)) := by
    intro i
    rw [Complex.div_im]
    simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, Complex.sub_re,
      zero_mul, zero_sub]
    field_simp
    ring
  have hsum_im : (∑ i, (r i : ℂ) / ((d i : ℂ) - z)).im
      = z.im * ∑ i, r i / Complex.normSq ((d i : ℂ) - z) := by
    rw [Complex.im_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  intro h
  have him0 : (∑ i, (r i : ℂ) / ((d i : ℂ) - z)).im = 0 := by rw [h]; simp
  rw [hsum_im] at him0
  exact (mul_ne_zero hz (ne_of_gt hpos)) him0

/-- **Localization of complex secular roots.** Contrapositive of `secular_roots_real_signed`: any off-axis
secular root `z` (`∑ r_i/(d_i−z)=1`, `Im z ≠ 0`) must lie in `{Φ ≤ 0}`, `Φ(z) = ∑ r_i/‖d_i−z‖²` — a
neighborhood of the negative-residue poles. So complex secular roots (= the off-line zeros / the faithful
integer `κ₋`) live only where the source `r` changes sign. Hence `RH ⟺ no secular root in {Φ ≤ 0}`. -/
theorem complex_root_in_Phi_nonpos {n : ℕ} (d r : Fin n → ℝ) (z : ℂ) (hz : z.im ≠ 0)
    (hroot : ∑ i, (r i : ℂ) / ((d i : ℂ) - z) = 1) :
    ∑ i, r i / Complex.normSq ((d i : ℂ) - z) ≤ 0 := by
  by_contra h
  exact secular_roots_real_signed d r z hz (not_le.mp h) hroot

end JensenLadder
