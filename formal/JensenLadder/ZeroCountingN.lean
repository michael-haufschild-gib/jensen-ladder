import Mathlib

/-!
# The Riemann zeta zero-counting function `N(T)` — foundation

Toward a Lean formalization of the **Riemann–von Mangoldt formula**
`N(T) = (T/2π) log (T/2π) − T/2π + O(log T)`,
which is currently ABSENT from mathlib (mathlib has `riemannZetaZeros` as a discrete set with
local finiteness — `Mathlib/NumberTheory/LSeries/ZetaZeros.lean` — but no counting function and
no asymptotic).

This module supplies the **foundation**: it defines the counting function `N T` (the number of
nontrivial zeros `ρ` of `ζ` with `0 ≤ Re ρ ≤ 1` and `0 < Im ρ ≤ T`), proves it is well-defined
(the relevant zero set is finite), and proves its basic order properties (monotone; vanishes for
`T ≤ 0`).  Well-definedness uses mathlib's `IsCompact.inter_riemannZetaZeros_finite`.

RH-agnostic and unconditional: `N T` and the eventual asymptotic hold regardless of RH.  This is
the off-the-wall, publication-aimed track (a formalization contribution).  It does NOT prove RH.

## Remaining targets (multi-session; documented, not yet formalized — NO sorries here)
* `N` via the argument principle: `N T = (1/2πi) ∮_∂R (ξ'/ξ)` for the box `R` (program already has
  the argument-principle count, quest task #26).
* main term `(T/2π) log(T/2π) − T/2π` from the Γ-factor of the completed `ξ`, via mathlib's
  `Stirling` / log-Γ asymptotics.
* error `S(T) = O(log T)` (Backlund/Jensen-circle), using the ξ vertical-strip / order bounds
  (`CompletedZetaStripBound`, `XiOrderBound`).
-/

namespace JensenLadder.ZeroCountingN

open Complex

/-- The nontrivial zeros of `ζ` in the critical strip with imaginary part in `(0, T]`. -/
noncomputable def zerosUpTo (T : ℝ) : Set ℂ :=
  {z | z ∈ riemannZetaZeros ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}

/-- The counting set is finite: it sits inside the compact strip-box `[0,1] × [0,T]`, and a
compact set meets the (discrete) zero set in a finite set (`IsCompact.inter_riemannZetaZeros_finite`). -/
theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite := by
  have hbox : IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ T} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_le continuous_const Complex.continuous_re
      apply IsClosed.inter
      · exact isClosed_le Complex.continuous_re continuous_const
      apply IsClosed.inter
      · exact isClosed_le continuous_const Complex.continuous_im
      · exact isClosed_le Complex.continuous_im continuous_const
    · apply ((Metric.isBounded_Icc (0 : ℝ) 1).reProdIm
        (Metric.isBounded_Icc (0 : ℝ) T)).subset
      intro z hz
      exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩
  apply (hbox.inter_riemannZetaZeros_finite).subset
  intro z hz
  exact ⟨⟨hz.2.1, hz.2.2.1, le_of_lt hz.2.2.2.1, hz.2.2.2.2⟩, hz.1⟩

/-- The Riemann zeta **zero-counting function** `N(T)`: the number of nontrivial zeros with
`0 < Im ρ ≤ T` in the critical strip. -/
noncomputable def N (T : ℝ) : ℕ := (zerosUpTo T).ncard

/-- `N` is monotone in the height `T`. -/
theorem N_mono : Monotone N := by
  intro a b hab
  apply Set.ncard_le_ncard _ (zerosUpTo_finite b)
  intro z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, le_trans hz.2.2.2.2 hab⟩

/-- There are no counted zeros at non-positive height. -/
theorem N_eq_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) : N T = 0 := by
  rw [N, Set.ncard_eq_zero (zerosUpTo_finite T)]
  ext z
  simp only [zerosUpTo, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, _, _, him, hleT⟩
  linarith

end JensenLadder.ZeroCountingN
