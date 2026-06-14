import JensenLadder.CVSKatoSmallNoGo

/-!
# Marginal C-vS limit handoff

This module records the distinction exposed by the semilocal C-vS screen:
finite-scale simplicity can hold while the isolation margin collapses in the
limit.

The finite row is useful:

```text
0 < gap(a)  ->  simple even bottom state at scale a.
```

But if the same gap is arbitrarily small, there is no uniform isolation floor
`epsilon <= gap(a)`.  Thus the C-vS engine can certify real-rooted finite
approximants, while the RH-bearing row is still the Hurwitz/CCM convergence to
`Xi`.

This file does not prove the finite gap positivity, the C-vS theorem, the
operator convergence row, or RH.  Evidence class: formal/certificate artifact
and dead-end-boundary calibration.  Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

namespace JensenLadder
namespace CVSMarginalLimit

open CVSSpectralRoute
open CVSGapPreservation
open CVSKatoSmallNoGo

universe u

/-- A scale-indexed gap has a uniform positive isolation floor. -/
def UniformIsolation {Scale : Type u} (gap : Scale -> ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ a : Scale, ε ≤ gap a

/-- An arbitrarily small gap has no uniform positive isolation floor. -/
theorem not_uniformIsolation_of_gapArbitrarilySmall
    {Scale : Type u}
    {gap : Scale -> ℝ}
    (hgap : GapArbitrarilySmall gap) :
    ¬ UniformIsolation gap := by
  rintro ⟨ε, hε, hfloor⟩
  rcases hgap ε hε with ⟨a, hsmall⟩
  linarith [hfloor a, hsmall]

/--
Finite C-vS gap data in the marginal regime: every finite gap is positive, so
the finite simple-even row is available, but the gap has no positive floor in
the scale limit.
-/
structure MarginalGroundStateData
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A) where
  gapData : GroundStateGapData G
  finiteGapPositive : PositiveGap gapData.gap
  gapArbitrarilySmall : GapArbitrarilySmall gapData.gap

namespace MarginalGroundStateData

/-- The finite positive gaps still supply the finite simple-even C-vS row. -/
theorem simpleEvenGroundStates
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : MarginalGroundStateData G) :
    SimpleEvenGroundStates G :=
  simpleEvenGroundStates_of_positiveGap D.gapData D.finiteGapPositive

/-- The marginal regime rules out a uniform isolation floor. -/
theorem not_uniformIsolation
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : MarginalGroundStateData G) :
    ¬ UniformIsolation D.gapData.gap :=
  not_uniformIsolation_of_gapArbitrarilySmall D.gapArbitrarilySmall

/-- Marginal finite gaps give finite simple-even data but no uniform isolation. -/
theorem simpleEvenGroundStates_and_not_uniformIsolation
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : MarginalGroundStateData G) :
    SimpleEvenGroundStates G ∧ ¬ UniformIsolation D.gapData.gap :=
  ⟨D.simpleEvenGroundStates, D.not_uniformIsolation⟩

/--
The marginal finite C-vS row proves RH only if the separate convergence row is
also supplied.
-/
theorem riemannHypothesis_of_convergence
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : MarginalGroundStateData G)
    (H : HurwitzXiConvergence A)
    (hconv : H.convergesToXi) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence G H
    D.simpleEvenGroundStates hconv

/--
If a non-real regular `Xi` zero exists, then the convergence row is false for
any marginal finite C-vS family whose finite gaps already supply simple-even
approximants.
-/
theorem not_convergence_of_nonrealRegularXiZero
    {A : FiniteScaleApproximants.{u}}
    {G : SimpleEvenGroundStateData A}
    (D : MarginalGroundStateData G)
    (H : HurwitzXiConvergence A)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ H.convergesToXi :=
  not_convergence_of_nonrealRegularXiZero_and_simpleEvenGroundStates
    G H D.simpleEvenGroundStates hz hzim

end MarginalGroundStateData

/--
Packaged marginal C-vS certificate.  The finite marginal row alone is below RH;
the field `convergesToXi` is the load-bearing spectral-identification input.
-/
structure MarginalCVSRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  marginalData : MarginalGroundStateData groundStateData
  convergesToXi : convergence.convergesToXi

namespace MarginalCVSRHCertificate

/-- A packaged marginal C-vS certificate proves mathlib's RH only through the
explicit convergence row. -/
theorem riemannHypothesis
    (cert : MarginalCVSRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.marginalData.riemannHypothesis_of_convergence
    cert.convergence cert.convergesToXi

/-- The packaged finite marginal row has no uniform isolation floor. -/
theorem not_uniformIsolation
    (cert : MarginalCVSRHCertificate.{u}) :
    ¬ UniformIsolation cert.marginalData.gapData.gap :=
  cert.marginalData.not_uniformIsolation

end MarginalCVSRHCertificate

end CVSMarginalLimit
end JensenLadder
