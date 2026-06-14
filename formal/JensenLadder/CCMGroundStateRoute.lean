import JensenLadder.DeterminantHurwitzRoute

/-!
# CCM ground-state route

This module refines the determinant Hurwitz route by naming the specific
ground-state/prolate rows isolated in the CCM spectral-triple program.

For the intended application, the exact finite identity says that the
regularized determinant is the Fourier transform of the ground state of the
truncated Weil form.  The limiting theorem then factors through two analytic
rows:

* the finite Weil-form ground state converges to the prolate ground state;
* the corresponding prolate/Fourier limit converges to `Xi`.

Those analytic rows are not proved here.  They are explicit hypotheses that
compose to the existing determinant-route row `locallyUniformToXi`.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMGroundStateRoute

universe u

/--
Ground-state/prolate data refining a determinant approximant family.

`State a` is an abstract state space at scale `a`.  The two vectors are carried
only so that the Lean interface names the intended analytic objects; the actual
metric, Fourier transform, and prolate operator are external analytic data.
-/
structure GroundStateProlateData
    (D : DeterminantHurwitzRoute.DeterminantApproximants.{u}) where
  State : D.Scale -> Type u
  groundState : (a : D.Scale) -> State a
  prolateState : (a : D.Scale) -> State a
  determinantGroundStateIdentity : Prop
  groundStateConvergesToProlate : Prop
  prolateFourierConvergesToXi : Prop
  determinantConvergence :
    DeterminantHurwitzRoute.DeterminantApproximants.HurwitzConvergence D
  locallyUniformToXi_of_groundState_rows :
    determinantGroundStateIdentity ->
      groundStateConvergesToProlate ->
        prolateFourierConvergesToXi ->
          determinantConvergence.locallyUniformToXi

namespace GroundStateProlateData

variable {D : DeterminantHurwitzRoute.DeterminantApproximants.{u}}

/-- The three CCM ground-state rows that imply determinant convergence to `Xi`. -/
def GroundStateRows (G : GroundStateProlateData D) : Prop :=
  G.determinantGroundStateIdentity ∧
    G.groundStateConvergesToProlate ∧
      G.prolateFourierConvergesToXi

/-- The ground-state rows assemble the determinant local-uniform convergence row. -/
theorem locallyUniformToXi_of_rows
    (G : GroundStateProlateData D)
    (hrows : G.GroundStateRows) :
    G.determinantConvergence.locallyUniformToXi :=
  G.locallyUniformToXi_of_groundState_rows hrows.1 hrows.2.1 hrows.2.2

/--
Finite determinant real-zero data plus the CCM ground-state rows prove
mathlib's `RiemannHypothesis` through the determinant Hurwitz route.
-/
theorem riemannHypothesis_of_groundStateRows
    (G : GroundStateProlateData D)
    (hreal :
      DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal D)
    (hrows : G.GroundStateRows) :
    RiemannHypothesis :=
  DeterminantHurwitzRoute.DeterminantApproximants.riemannHypothesis_of_allZerosReal_and_locallyUniform
      D G.determinantConvergence hreal (G.locallyUniformToXi_of_rows hrows)

/--
A non-real regular `Xi` zero refutes the ground-state-to-prolate row if the
finite determinant real-zero row, the determinant identity row, and the
prolate/Fourier row are kept fixed.
-/
theorem not_groundStateConvergesToProlate_of_nonrealRegularXiZero_and_rows
    (G : GroundStateProlateData D)
    (hreal :
      DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal D)
    (hid : G.determinantGroundStateIdentity)
    (hpro : G.prolateFourierConvergesToXi)
    {z : Complex}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ G.groundStateConvergesToProlate := by
  intro hgs
  have hloc : G.determinantConvergence.locallyUniformToXi :=
    G.locallyUniformToXi_of_groundState_rows hid hgs hpro
  exact (DeterminantHurwitzRoute.DeterminantApproximants.not_locallyUniformToXi_of_nonrealRegularXiZero_and_allZerosReal
      D G.determinantConvergence hreal hz hzim) hloc

/-- A non-real regular `Xi` zero refutes the full three-row CCM package. -/
theorem not_groundStateRows_of_nonrealRegularXiZero
    (G : GroundStateProlateData D)
    (hreal :
      DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal D)
    {z : Complex}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ G.GroundStateRows := by
  rintro ⟨hid, hgs, hpro⟩
  exact G.not_groundStateConvergesToProlate_of_nonrealRegularXiZero_and_rows
    hreal hid hpro hz hzim hgs

end GroundStateProlateData

/-- Packaged CCM ground-state/prolate route certificate. -/
structure GroundStateProlateRHCertificate where
  determinants : DeterminantHurwitzRoute.DeterminantApproximants.{u}
  data : GroundStateProlateData determinants
  allZerosReal :
    DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal determinants
  determinantGroundStateIdentity : data.determinantGroundStateIdentity
  groundStateConvergesToProlate : data.groundStateConvergesToProlate
  prolateFourierConvergesToXi : data.prolateFourierConvergesToXi

namespace GroundStateProlateRHCertificate

/-- The packaged three-row CCM data. -/
theorem groundStateRows
    (cert : GroundStateProlateRHCertificate.{u}) :
    cert.data.GroundStateRows :=
  ⟨cert.determinantGroundStateIdentity,
    cert.groundStateConvergesToProlate,
    cert.prolateFourierConvergesToXi⟩

/--
A packaged CCM ground-state/prolate certificate proves mathlib's
`RiemannHypothesis`.
-/
theorem riemannHypothesis
    (cert : GroundStateProlateRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.data.riemannHypothesis_of_groundStateRows
    cert.allZerosReal cert.groundStateRows

end GroundStateProlateRHCertificate

/--
Packaged obstruction: with determinant real-zero data, determinant identity, and
prolate/Fourier convergence fixed, a non-real regular `Xi` zero forces the
ground-state-to-prolate row to fail.
-/
structure GroundStateProlateFalsifier where
  determinants : DeterminantHurwitzRoute.DeterminantApproximants.{u}
  data : GroundStateProlateData determinants
  allZerosReal :
    DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal determinants
  determinantGroundStateIdentity : data.determinantGroundStateIdentity
  prolateFourierConvergesToXi : data.prolateFourierConvergesToXi
  badZero : Complex
  badZero_regular : RHReduction.riemannXiRegularZero badZero
  badZero_nonreal : badZero.im ≠ 0

namespace GroundStateProlateFalsifier

/-- The packaged obstruction refutes ground-state convergence to the prolate row. -/
theorem not_groundStateConvergesToProlate
    (cert : GroundStateProlateFalsifier.{u}) :
    ¬ cert.data.groundStateConvergesToProlate :=
  cert.data.not_groundStateConvergesToProlate_of_nonrealRegularXiZero_and_rows
    cert.allZerosReal cert.determinantGroundStateIdentity
    cert.prolateFourierConvergesToXi cert.badZero_regular cert.badZero_nonreal

/-- The packaged obstruction refutes the full three-row CCM package. -/
theorem not_groundStateRows
    (cert : GroundStateProlateFalsifier.{u}) :
    ¬ cert.data.GroundStateRows :=
  cert.data.not_groundStateRows_of_nonrealRegularXiZero
    cert.allZerosReal cert.badZero_regular cert.badZero_nonreal

/-- The same non-real regular `Xi` zero refutes mathlib's RH directly. -/
theorem not_riemannHypothesis
    (cert : GroundStateProlateFalsifier.{u}) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact cert.badZero_nonreal
    ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      hRH cert.badZero cert.badZero_regular)

end GroundStateProlateFalsifier

end CCMGroundStateRoute
end JensenLadder
