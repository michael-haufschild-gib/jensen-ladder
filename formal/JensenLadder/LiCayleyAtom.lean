/-
# Li criterion via the Cayley map — on-line positivity atom (RH-free, axiom-clean)

Author: berry, 2026-06-18. Program: `program_T3_T5_self_product_construction` (Li-criterion vehicle).

Bombieri–Lagarias: RH ⟺ `λ_n ≥ 0 ∀n`, `λ_n = Σ_ρ [1 − (1−1/ρ)^n]`. With the Cayley image `w = 1 − 1/ρ`
(proven elsewhere: `Re ρ = ½ ⟺ |w| = 1`), this file formalizes:

* `cayley_fe_inversion` — the functional equation `ρ ↦ 1−ρ` acts on the Cayley variable as `w ↦ 1/w`
  (so zeros sit in quartets `{w, w̄, 1/w, 1/w̄}`, collapsing to a unit-circle pair on the line);
* `li_pair_eq` — a conjugate pair contributes `(1−wⁿ)+(1−w̄ⁿ) = 2 − 2·Re(wⁿ)` to `λ_n`;
* `li_pair_nonneg` — for an **on-line** pair (`‖w‖=1`), that contribution is **non-negative**
  (`Re(wⁿ) ≤ ‖wⁿ‖ = 1`). This is the per-pair core of `RH ⟹ λ_n ≥ 0`.

These are RH-free. They do NOT prove `λ_n ≥ 0` (that needs the zeros on the line = RH); they formalize the
positivity *atom* of the easy direction and the FE structure of the Cayley quartet.
-/
import Mathlib

open Complex

namespace LiCayleyAtom

/-- The functional equation `ρ ↦ 1−ρ` acts on the Cayley variable `w(ρ)=1−1/ρ` as inversion `w ↦ 1/w`,
stated in product form: `w(1−ρ) · w(ρ) = 1`. -/
theorem cayley_fe_inversion (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (1 - 1 / (1 - ρ)) * (1 - 1 / ρ) = 1 := by
  have hned : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- A conjugate pair `{ρ, ρ̄}` (Cayley images `w, w̄`) contributes `2 − 2·Re(wⁿ)` to the n-th Li coefficient. -/
theorem li_pair_eq (w : ℂ) (n : ℕ) :
    ((1 - w ^ n) + (1 - (starRingEnd ℂ w) ^ n)).re = 2 - 2 * (w ^ n).re := by
  have h : ((starRingEnd ℂ w) ^ n).re = (w ^ n).re := by
    rw [← map_pow]; exact Complex.conj_re (w ^ n)
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, h]; ring

/-- On-line per-pair Li positivity: if `‖w‖ = 1` (the Cayley image of an on-critical-line zero), the
conjugate-pair contribution `2 − 2·Re(wⁿ)` is non-negative. The per-pair core of `RH ⟹ λ_n ≥ 0`. -/
theorem li_pair_nonneg (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ 2 - 2 * (w ^ n).re := by
  have h1 : (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
  have h2 : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  rw [h2] at h1
  linarith

/-- **Content-freeness of Cayley unitarity (HP–Cayley falsification, Branch A).**
Every real `x` (an eigenvalue of a Hermitian operator) Cayley-maps to the unit circle, *regardless of RH*.
Hence a Hermitian operator's Cayley transform has spectrum on the circle unconditionally — so "Cayley(H) is
unitary" carries no RH information when `H` is self-adjoint. (`x − i = conj(x + i)` for real `x`, and
`‖conj z‖ = ‖z‖`.) See `docs/rh/berry_hp_cayley_falsification_20260618.md`. -/
theorem cayley_real_on_circle (x : ℝ) :
    ‖((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)‖ = 1 := by
  have hne : (x : ℂ) + Complex.I ≠ 0 := by
    intro h
    have h2 : ((x : ℂ) + Complex.I).im = 0 := by rw [h]; simp
    simp at h2
  have hconj : (starRingEnd ℂ) ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    simp [map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  rw [norm_div, ← hconj, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

end LiCayleyAtom
