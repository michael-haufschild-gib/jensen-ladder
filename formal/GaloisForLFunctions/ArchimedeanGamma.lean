import GaloisForLFunctions.Core
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Archimedean Gamma recurrence and connection compatibility

This file formalizes the Gamma/digamma scalar identities used in
`completed-base-archimedean-coordinate.md`.

It proves the exact `s ↦ s+2` recurrence for Deligne's real archimedean Gamma
factor and the half-argument digamma recurrence that makes the Gamma connection
compatible with the archimedean shift multiplier. It does not construct the
full completed difference-differential ring `R+`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Logarithmic connection coefficient for Deligne's real archimedean Gamma
factor, `-1/2 log pi + 1/2 psi(s/2)`. -/
def gammaRealLogConnection (s : ℂ) : ℂ :=
  -(((Real.log Real.pi : ℝ) : ℂ) / 2) + Complex.digamma (s / 2) / 2

/-- Deligne's real archimedean Gamma factor satisfies the `s ↦ s+2`
recurrence used by the completed base: `Gamma_R(s+2)=(s/(2*pi)) Gamma_R(s)`. -/
theorem gammaReal_shift_two {s : ℂ} (hs : s ≠ 0) :
    Complex.Gammaℝ (s + 2) = (s / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ s := by
  rw [Complex.Gammaℝ_add_two hs]
  field_simp [two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Digamma recurrence in the half-argument form used by the completed base. -/
theorem digamma_half_add_one {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    Complex.digamma (s / 2 + 1) = Complex.digamma (s / 2) + 2 / s := by
  have hs0 : s ≠ 0 := by
    intro h
    have h0 := hs 0
    simp [h] at h0
  rw [Complex.digamma_apply_add_one (s / 2) hs]
  field_simp [hs0]

/-- The Gamma-log connection coefficient is compatible with the archimedean
shift multiplier. This is the scalar identity behind
`d/ds ((s/(2*pi))g) = sigma_infty (d/ds g)` after cancelling the nonzero symbol
`g`. -/
theorem gammaRealLogConnection_shift_compat {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    (1 / (2 * (Real.pi : ℂ))) + (s / (2 * (Real.pi : ℂ))) * gammaRealLogConnection s =
      (s / (2 * (Real.pi : ℂ))) * gammaRealLogConnection (s + 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    have h0 := hs 0
    simp [h] at h0
  unfold gammaRealLogConnection
  rw [show (s + 2) / 2 = s / 2 + 1 by ring]
  rw [digamma_half_add_one hs]
  field_simp [hs0, two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

end

end GaloisForLFunctions
