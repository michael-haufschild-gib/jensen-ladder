import JensenLadder.SquaredDeterminantApproximation
import JensenLadder.SquaredDeterminantGauge

/-!
# Squared determinant zero transfer

This module connects the gauge-cancelled paired determinant identity to the
squared-variable approximation consumer.

If finite gauge models satisfy

```text
  squareDet_a(y^2) = c_a * F_a(y)^2
```

then zeros of the target functions `F_a` transfer to zeros of the squared
determinants at `w = y^2`.  Consequently, variable-level Hurwitz shadowing of
regular `Xi` zeros by `F_a` zeros supplies the squared zero-shadowing row
consumed by `SquaredDeterminantApproximation`.

This is only zero-transfer bookkeeping for the squared target.  It does not
prove the variable-level shadowing row, nonnegative squared spectrum,
determinant convergence, the order-`1/2` Hadamard theorem, or RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantZeroTransfer

open Filter Topology

universe u

/-- A finite-scale family of paired gauge models. -/
structure PairedGaugeApproximants where
  Scale : Type u
  model : Scale -> SquaredDeterminantGauge.PairedGaugeModel

namespace PairedGaugeApproximants

/-- The squared-variable determinants associated to a paired gauge family. -/
def squaredDeterminants (G : PairedGaugeApproximants.{u}) :
    SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u} where
  Scale := G.Scale
  determinant := fun a w => (G.model a).squareDet w

/--
Variable-level zero shadowing for the gauge-cancelled targets.

For every regular `Xi` zero `z`, finite target zeros `y_n` converge to `z`.
The squared transfer below turns these into squared determinant zeros converging
to `z^2`.
-/
def RegularXiVariableZeroShadowing
    (G : PairedGaugeApproximants.{u}) (scale : ℕ -> G.Scale) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
    ∃ y : ℕ -> ℂ,
      (∀ n : ℕ, (G.model (scale n)).approximant (y n) = 0) ∧
        Tendsto y atTop (𝓝 z)

/--
Variable-level target zero shadowing implies squared determinant zero shadowing.

This is the formal handoff from a Hurwitz argument in the original `z` variable
to the `w = z^2` determinant consumer.
-/
theorem regularXiSquaredZeroShadowing_of_variableZeroShadowing
    (G : PairedGaugeApproximants.{u}) (scale : ℕ -> G.Scale)
    (hshadow : G.RegularXiVariableZeroShadowing scale) :
    (G.squaredDeterminants).RegularXiSquaredZeroShadowing scale := by
  intro z hz
  rcases hshadow z hz with ⟨y, hyzero, hytend⟩
  refine ⟨fun n : ℕ => y n ^ 2, ?_, ?_⟩
  · intro n
    exact (G.model (scale n)).squareDet_eq_zero_of_approximant_eq_zero (hyzero n)
  · simpa using hytend.pow 2

/--
Finite nonnegative-real squared determinant zeros plus variable-level shadowing
force all regular `Xi` zeros to be real.
-/
theorem regular_xi_zeros_real_of_variableZeroShadowing
    (G : PairedGaugeApproximants.{u}) (scale : ℕ -> G.Scale)
    (hnonneg : (G.squaredDeterminants).AllZerosNonnegativeReal)
    (hshadow : G.RegularXiVariableZeroShadowing scale) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z -> z.im = 0 :=
  (G.squaredDeterminants).regular_xi_zeros_real_of_shadowing scale hnonneg
    (G.regularXiSquaredZeroShadowing_of_variableZeroShadowing scale hshadow)

/--
The paired-gauge zero-transfer bridge proves mathlib's `RiemannHypothesis` once
the squared spectrum is nonnegative and the target zeros shadow regular `Xi`
zeros in the original variable.
-/
theorem riemannHypothesis_of_variableZeroShadowing
    (G : PairedGaugeApproximants.{u}) (scale : ℕ -> G.Scale)
    (hnonneg : (G.squaredDeterminants).AllZerosNonnegativeReal)
    (hshadow : G.RegularXiVariableZeroShadowing scale) :
    RiemannHypothesis :=
  (G.squaredDeterminants).riemannHypothesis_of_shadowing scale hnonneg
    (G.regularXiSquaredZeroShadowing_of_variableZeroShadowing scale hshadow)

/--
A nonreal regular `Xi` zero refutes variable-level shadowing whenever all finite
squared determinant zeros lie on the nonnegative real ray.
-/
theorem not_variableZeroShadowing_of_nonrealRegularXiZero
    (G : PairedGaugeApproximants.{u}) (scale : ℕ -> G.Scale)
    (hnonneg : (G.squaredDeterminants).AllZerosNonnegativeReal) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) (hzim : z.im ≠ 0) :
    ¬ G.RegularXiVariableZeroShadowing scale := by
  intro hshadow
  exact hzim
    (G.regular_xi_zeros_real_of_variableZeroShadowing scale hnonneg hshadow z hz)

end PairedGaugeApproximants

/-- Packaged paired-gauge squared determinant zero-transfer certificate. -/
structure PairedGaugeZeroTransferCertificate where
  family : PairedGaugeApproximants.{u}
  scale : ℕ -> family.Scale
  allZerosNonnegativeReal : family.squaredDeterminants.AllZerosNonnegativeReal
  variableZeroShadowing : family.RegularXiVariableZeroShadowing scale

namespace PairedGaugeZeroTransferCertificate

/-- A packaged paired-gauge zero-transfer certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : PairedGaugeZeroTransferCertificate.{u}) :
    RiemannHypothesis :=
  cert.family.riemannHypothesis_of_variableZeroShadowing cert.scale
    cert.allZerosNonnegativeReal cert.variableZeroShadowing

end PairedGaugeZeroTransferCertificate

end SquaredDeterminantZeroTransfer
end JensenLadder
