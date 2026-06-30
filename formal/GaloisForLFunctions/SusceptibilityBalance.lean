import GaloisForLFunctions.Core

/-!
# Susceptibility mirror-frequency balance

This file formalizes the elementary exponent calculation from the
prime-zero susceptibility ticket: for a finite multiplicity `m`, the
mirror-frequency factor has exponent `(1 - 2 * beta) / m`, and frequency
independence forces that exponent to vanish, equivalently `beta = 1 / 2`.

It does not formalize the implicit-function/Puiseux zero splitting, the zeta
functional equation, or the curvature-hierarchy identification.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The `n`-dependent part of the mirror-pair susceptibility ratio. -/
def susceptibilityMirrorFrequencyFactor (beta : ℝ) (m : ℕ) (n : ℝ) : ℝ :=
  n ^ ((1 - 2 * beta) / (m : ℝ))

/-- The susceptibility exponent vanishes exactly on the critical line. -/
theorem susceptibilityExponent_zero_iff {beta : ℝ} {m : ℕ} (hm : m ≠ 0) :
    ((1 - 2 * beta) / (m : ℝ) = 0) ↔ beta = 1 / 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  constructor
  · intro h
    have hnum : 1 - 2 * beta = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right hmR
    linarith
  · intro h
    subst beta
    norm_num

/-- The mirror-frequency factor is independent of every probe frequency `n > 1`
exactly on the critical line. -/
theorem susceptibilityMirrorFrequencyFactor_eq_one_forall_iff {beta : ℝ} {m : ℕ}
    (hm : m ≠ 0) :
    (∀ n : ℝ, 1 < n → susceptibilityMirrorFrequencyFactor beta m n = 1) ↔
      beta = 1 / 2 := by
  constructor
  · intro h
    have h2 : (2 : ℝ) ^ ((1 - 2 * beta) / (m : ℝ)) = 1 := by
      simpa [susceptibilityMirrorFrequencyFactor] using h 2 one_lt_two
    have hlog := congrArg Real.log h2
    rw [Real.log_rpow zero_lt_two, Real.log_one] at hlog
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hexp : (1 - 2 * beta) / (m : ℝ) = 0 := by
      exact (mul_eq_zero.mp hlog).resolve_right hlog2
    exact (susceptibilityExponent_zero_iff hm).mp hexp
  · intro h n hn
    subst beta
    simp [susceptibilityMirrorFrequencyFactor]

end

end GaloisForLFunctions
