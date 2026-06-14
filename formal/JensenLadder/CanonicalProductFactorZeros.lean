import JensenLadder.CanonicalProductGenusOne

/-!
# Zeros of the genus-1 elementary factor (reverse-bridge ingredient)

Companion to `CanonicalProductGenusOne` (the convergence side). For the genus-1 canonical
product `∏ₙ E₁(z/aₙ)` to be the Hadamard factor of an entire function with prescribed zero
set `{aₙ}`, two facts are needed: locally-uniform convergence (proved there), and that each
factor vanishes *exactly* at its prescribed zero. This file supplies the second:

  `E₁(w) = 0 ↔ w = 1`,  hence  `E₁(z/a) = 0 ↔ z = a`  (for `a ≠ 0`).

So the `n`-th factor of the canonical product vanishes exactly at `z = aₙ` and nowhere else
(`exp` never vanishes). This is the "correct zeros" half of the Hadamard ingredient; it does
**not** discharge `hconv`.

Evidence class: proved lemma / formal artifact. Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

open Complex

namespace JensenLadder.CanonicalProductGenusOne

/-- The genus-1 elementary factor `E₁(w) = (1−w)·exp w` vanishes exactly at `w = 1`
(`exp` is nowhere zero). -/
@[simp] lemma E1_eq_zero_iff {w : ℂ} : E1 w = 0 ↔ w = 1 := by
  unfold E1
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (Complex.exp_ne_zero w)
  · rintro rfl
    left; ring

/-- The `a`-th canonical-product factor `E₁(z/a)` vanishes exactly at `z = a` (for `a ≠ 0`). -/
lemma E1_div_eq_zero_iff {z a : ℂ} (ha : a ≠ 0) : E1 (z / a) = 0 ↔ z = a := by
  rw [E1_eq_zero_iff, div_eq_one_iff_eq ha]

/-- Off its prescribed zero, the `a`-th factor is nonzero. -/
lemma E1_div_ne_zero {z a : ℂ} (ha : a ≠ 0) (hz : z ≠ a) : E1 (z / a) ≠ 0 := by
  rw [Ne, E1_div_eq_zero_iff ha]; exact hz

end JensenLadder.CanonicalProductGenusOne
