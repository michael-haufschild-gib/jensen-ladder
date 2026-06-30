import GaloisForLFunctions.RankOneCohomology

/-!
# Multiplier dichotomy: CC gauge-trivialization anchor

This file formalizes the elementary gauge calculation from
`docs/drafts/pipeline/2-fully-proven/multiplier-dichotomy-theorem.md`.

If a rank-one multiplier is constant up to coboundary,
`a = c * σ(g) / g`, then gauging by `1/g` changes the multiplier to the
constant `c`. This is the algebraic core of case (I) in the paper proof.

The Picard-Vessiot classification, degree-at-infinity obstruction, and imported
hypertranscendence converse are not formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **CC gauge-trivialization identity.** If `a = c * σ(g) / g`, then the
gauge `h = 1/g` sends the multiplier to `c`:
`a * σ(h) / h = c`. Written in group notation, division is multiplication by
inverse. -/
theorem ccGaugeMultiplier_eq_const {G : Type*} [CommGroup G]
    (σ : G →* G) (c g : G) :
    (c * (σ g * g⁻¹)) * (σ g⁻¹ * (g⁻¹)⁻¹) = c := by
  simp [map_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Local ODE form of the case-(I) solution `f(z)=g(z) exp(z*lam)`.
If `g` has derivative `g'` and `g z ≠ 0`, then `f' =
(g'/g + lam) f` at `z`. This is the analytic core of the card's
`f'/f = g'/g + log c` statement, with `lam = log c`. -/
theorem hasDerivAt_mul_exp_const_ode {g : ℂ → ℂ} {g' lam z : ℂ}
    (hg : HasDerivAt g g' z) (hgz : g z ≠ 0) :
    HasDerivAt (fun w : ℂ => g w * Complex.exp (w * lam))
      (((g' / g z) + lam) * (g z * Complex.exp (z * lam))) z := by
  have hlin : HasDerivAt (fun w : ℂ => w * lam) lam z := by
    simpa using (hasDerivAt_id z).mul_const lam
  have hprod := hg.mul hlin.cexp
  have hderiv :
      g' * Complex.exp (z * lam) + g z * (Complex.exp (z * lam) * lam) =
        ((g' / g z) + lam) * (g z * Complex.exp (z * lam)) := by
    field_simp [hgz]
  simpa [Pi.mul_apply, hderiv] using hprod

/-- Global shift form of the case-(I) solution.
If `c = exp lam` and `a(z) = c * g(z+1) / g(z)`, then
`f(z)=g(z) exp(z*lam)` satisfies `f(z+1)=a(z) f(z)` at every point where
`g z` is nonzero. -/
theorem ccShiftSolution_eq (g : ℂ → ℂ) (lam z : ℂ) (hgz : g z ≠ 0) :
    g (z + 1) * Complex.exp ((z + 1) * lam) =
      (Complex.exp lam * (g (z + 1) / g z)) * (g z * Complex.exp (z * lam)) := by
  rw [show (z + 1) * lam = z * lam + lam by ring]
  rw [Complex.exp_add]
  field_simp [hgz]

end

end GaloisForLFunctions
