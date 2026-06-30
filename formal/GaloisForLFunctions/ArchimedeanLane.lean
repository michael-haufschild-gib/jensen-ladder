import GaloisForLFunctions.Core

/-!
# The archimedean shift as the diagonal of the prime lanes

This file formalizes the elementary, exact part of
`docs/drafts/the-archimedean-lane.md` §2:

`x_p = p^{-s}` is carried by the additive shift `s ↦ s+1` to
`p^{-(s+1)} = p^{-1} p^{-s}`. Thus the archimedean shift acts on every
prime Bohr coordinate by the corresponding prime-lane dilation.

This is only the finite algebraic coordinate identity. It does not formalize
the Gamma-factor shift, a completed Tannakian category, the functional equation,
or any RH/positivity claim.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Per-prime diagonal shift.** In the Bohr coordinate `x_p = p^{-s}`, the
additive shift `s ↦ s+1` is exactly the prime-lane dilation
`x_p ↦ p^{-1}x_p`. -/
theorem primeDiagonal_shift_apply (p : Nat.Primes) (s : ℂ) :
    ((p : ℂ) ^ (-(s + 1))) = ((p : ℂ)⁻¹) * ((p : ℂ) ^ (-s)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [show -(s + 1) = -s - 1 by ring]
  rw [Complex.cpow_sub (-s) 1 hpC]
  simp [div_eq_mul_inv, mul_comm]

/-- **The shift is the diagonal of the prime lanes.** As a function of all
prime coordinates, `s ↦ s+1` sends `p ↦ p^{-s}` to
`p ↦ p^{-1}p^{-s}` simultaneously for every prime. -/
theorem primeDiagonal_shift (s : ℂ) :
    (fun p : Nat.Primes => ((p : ℂ) ^ (-(s + 1)))) =
      fun p : Nat.Primes => ((p : ℂ)⁻¹) * ((p : ℂ) ^ (-s)) := by
  funext p
  exact primeDiagonal_shift_apply p s

end

end GaloisForLFunctions
