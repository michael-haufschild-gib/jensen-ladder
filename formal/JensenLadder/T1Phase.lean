import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# T1 phase-margin consumer algebra

This module formalizes the deterministic bulk T1 consumer used by the
Structure-Theorem route.  If the consecutive section pair has a certified phase
representation whose normalized Wronskian is `main + D`, and the remainder `D`
is strictly smaller than the phase main term, then the bulk Wronskian is
nonzero.

The xi-specific work -- deriving the phase representation, choosing bulk cells,
and filling the E1/E2/E4/E5 constants -- is not done here.

## Honest scope

This proves only the algebraic phase-margin implication.  It is not a proof of
T1 for the Riemann xi function, `CV(d)`, global xi-Jensen hyperbolicity, or the
Riemann Hypothesis.  Theorem M is proven, but Theorem M does not prove RH by
itself.
-/

namespace JensenLadder
namespace T1Phase

/-- The certificate-side remainder budget from the T1 note.  Producer rows may
prove `|D| <= remainderBudget ...`; this module only consumes that bound. -/
def remainderBudget
    (rho0 rho1 rho0p rho1p sigmap Phi Lambda : ℝ) : ℝ :=
  Phi * rho1
    + rho0p * (1 + rho1)
    + sigmap
    + rho0 * (Phi + sigmap)
    + (1 + rho0) * rho1p
    + Lambda * (1 + rho0) * (1 + rho1)

/-- If `|D| < |main|`, then the normalized Wronskian factor `main + D` is
nonzero. -/
theorem main_add_remainder_ne_zero_of_abs_lt
    {main D : ℝ}
    (hmargin : |D| < |main|) :
    main + D ≠ 0 := by
  intro hzero
  have hD : D = -main := by linarith
  have habs : |D| = |main| := by
    rw [hD, abs_neg]
  linarith

/-- Exact algebraic T1 decomposition.

Here `sphi`, `cphi`, `sphiPsi`, and `cphiPsi` stand for the sine/cosine values
of `phi` and `phi+psi`.  The only trigonometric input needed by this consumer is
the displayed identity
`cphi * sphiPsi - sphi * cphiPsi = sinPsi`. -/
theorem normalized_wronskian_decomposition
    {u v phip psip r0 r1 r0p r1p sphi cphi sphiPsi cphiPsi sinPsi Lambda W D : ℝ}
    (hu : u = sphi + r0)
    (hv : v = sphiPsi + r1)
    (htrig : cphi * sphiPsi - sphi * cphiPsi = sinPsi)
    (hW :
      W = (phip * cphi + r0p) * v
        - u * ((phip + psip) * cphiPsi + r1p)
        + Lambda * u * v)
    (hD :
      D = phip * cphi * r1
        + r0p * v
        - sphi * psip * cphiPsi
        - r0 * (phip + psip) * cphiPsi
        - u * r1p
        + Lambda * u * v) :
    W = phip * sinPsi + D := by
  subst u
  subst v
  rw [hW, hD, ← htrig]
  ring

/-- A strict phase-margin certificate excludes a bulk Wronskian root once the
Wronskian factors as `A * B * (main + D)` with nonzero amplitudes. -/
theorem wronskian_ne_zero_of_phase_margin
    {A B W main D : ℝ}
    (hA : A ≠ 0)
    (hB : B ≠ 0)
    (hW : W = A * B * (main + D))
    (hmargin : |D| < |main|) :
    W ≠ 0 := by
  intro hzero
  have hprod : A * B * (main + D) = 0 := by
    simpa [hW] using hzero
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  have hmain : main + D = 0 := by
    rcases mul_eq_zero.mp hprod with hABzero | hmainzero
    · exact False.elim (hAB hABzero)
    · exact hmainzero
  exact (main_add_remainder_ne_zero_of_abs_lt hmargin) hmain

/-- Positive-amplitude version of `wronskian_ne_zero_of_phase_margin`. -/
theorem wronskian_ne_zero_of_phase_margin_pos
    {A B W main D : ℝ}
    (hA_pos : 0 < A)
    (hB_pos : 0 < B)
    (hW : W = A * B * (main + D))
    (hmargin : |D| < |main|) :
    W ≠ 0 :=
  wronskian_ne_zero_of_phase_margin
    (ne_of_gt hA_pos) (ne_of_gt hB_pos) hW hmargin

/-- Certificate wrapper: if a producer has certified `|D| <= Err` and
`Err < |main|`, then the bulk Wronskian is nonzero. -/
theorem wronskian_ne_zero_of_remainder_bound
    {A B W main D Err : ℝ}
    (hA_pos : 0 < A)
    (hB_pos : 0 < B)
    (hW : W = A * B * (main + D))
    (hD : |D| ≤ Err)
    (hErr : Err < |main|) :
    W ≠ 0 :=
  wronskian_ne_zero_of_phase_margin_pos
    hA_pos hB_pos hW (lt_of_le_of_lt hD hErr)

/-- Certificate wrapper using the named seven-row T1 budget.  This theorem does
not prove the seven-row bound; it consumes it. -/
theorem wronskian_ne_zero_of_budget
    {A B W main D rho0 rho1 rho0p rho1p sigmap Phi Lambda : ℝ}
    (hA_pos : 0 < A)
    (hB_pos : 0 < B)
    (hW : W = A * B * (main + D))
    (hD : |D| ≤ remainderBudget rho0 rho1 rho0p rho1p sigmap Phi Lambda)
    (hBudget : remainderBudget rho0 rho1 rho0p rho1p sigmap Phi Lambda < |main|) :
    W ≠ 0 :=
  wronskian_ne_zero_of_remainder_bound hA_pos hB_pos hW hD hBudget

end T1Phase
end JensenLadder
