import JensenLadder.CCMGroundStateRoute
import Mathlib.Tactic

/-!
# CCM ground-state error route

This module refines the CCM ground-state/prolate row by adding an explicit
scale-indexed error budget.

The predicate `ErrorArbitrarilySmall err` is intentionally filter-free: it only
records that the proposed ground-state/prolate error can be made smaller than
every positive threshold somewhere in the scale family.  A concrete CCM proof
would replace this with the appropriate topology/filter theorem.  This finite
interface is still useful because it:

* gives a measurable row that implies `groundStateConvergesToProlate`;
* packages the resulting RH handoff through `CCMGroundStateRoute`;
* records the elementary obstruction that a positive error floor blocks this
  route.

Evidence class: formal/certificate artifact and dead-end elimination.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMGroundStateError

universe u

/-- A scale-indexed error can be made smaller than every positive threshold. -/
def ErrorArbitrarilySmall {Scale : Type u} (err : Scale -> ℝ) : Prop :=
  forall eps : ℝ, 0 < eps -> exists a : Scale, err a < eps

/-- A scale-indexed error has a positive lower floor. -/
def ErrorHasPositiveFloor {Scale : Type u} (err : Scale -> ℝ) : Prop :=
  exists eps0 : ℝ, 0 < eps0 ∧ forall a : Scale, eps0 <= err a

/-- A positive error floor blocks the arbitrarily-small-error row. -/
theorem not_errorArbitrarilySmall_of_errorHasPositiveFloor
    {Scale : Type u}
    {err : Scale -> ℝ}
    (hfloor : ErrorHasPositiveFloor err) :
    ¬ ErrorArbitrarilySmall err := by
  intro hsmall
  rcases hfloor with ⟨eps0, heps0, hfloor⟩
  rcases hsmall eps0 heps0 with ⟨a, hsmall_a⟩
  linarith [hfloor a, hsmall_a]

/-- Equivalently, an arbitrarily-small error has no positive lower floor. -/
theorem not_errorHasPositiveFloor_of_errorArbitrarilySmall
    {Scale : Type u}
    {err : Scale -> ℝ}
    (hsmall : ErrorArbitrarilySmall err) :
    ¬ ErrorHasPositiveFloor err := by
  intro hfloor
  exact not_errorArbitrarilySmall_of_errorHasPositiveFloor hfloor hsmall

/--
Quantitative data for the CCM ground-state/prolate row.

`error` is the proposed finite-scale distance or defect between the truncated
Weil-form ground state and the prolate ground state.  The field is the analytic
bridge from making that error arbitrarily small to the abstract
`groundStateConvergesToProlate` row used by `CCMGroundStateRoute`.
-/
structure GroundStateErrorData
    {D : DeterminantHurwitzRoute.DeterminantApproximants.{u}}
    (G : CCMGroundStateRoute.GroundStateProlateData D) where
  error : D.Scale -> ℝ
  groundStateConvergesToProlate_of_errorArbitrarilySmall :
    ErrorArbitrarilySmall error -> G.groundStateConvergesToProlate

namespace GroundStateErrorData

variable {D : DeterminantHurwitzRoute.DeterminantApproximants.{u}}
variable {G : CCMGroundStateRoute.GroundStateProlateData D}

/-- Arbitrarily small ground-state error supplies the prolate convergence row. -/
theorem groundStateConvergesToProlate
    (E : GroundStateErrorData G)
    (hsmall : ErrorArbitrarilySmall E.error) :
    G.groundStateConvergesToProlate :=
  E.groundStateConvergesToProlate_of_errorArbitrarilySmall hsmall

/-- Error control plus the other CCM rows supplies the full ground-state package. -/
theorem groundStateRows_of_errorArbitrarilySmall
    (E : GroundStateErrorData G)
    (hid : G.determinantGroundStateIdentity)
    (hsmall : ErrorArbitrarilySmall E.error)
    (hpro : G.prolateFourierConvergesToXi) :
    G.GroundStateRows :=
  ⟨hid, E.groundStateConvergesToProlate hsmall, hpro⟩

/--
Finite determinant real-zero data plus arbitrarily small ground-state/prolate
error proves mathlib's `RiemannHypothesis` through the CCM ground-state route.
-/
theorem riemannHypothesis_of_errorArbitrarilySmall
    (E : GroundStateErrorData G)
    (hreal :
      DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal D)
    (hid : G.determinantGroundStateIdentity)
    (hsmall : ErrorArbitrarilySmall E.error)
    (hpro : G.prolateFourierConvergesToXi) :
    RiemannHypothesis :=
  CCMGroundStateRoute.GroundStateProlateData.riemannHypothesis_of_groundStateRows
      G hreal (E.groundStateRows_of_errorArbitrarilySmall hid hsmall hpro)

/--
A non-real regular `Xi` zero refutes the arbitrarily-small ground-state error
row if the finite determinant real-zero row, determinant identity row, and
prolate/Fourier row are kept fixed.
-/
theorem not_errorArbitrarilySmall_of_nonrealRegularXiZero_and_rows
    (E : GroundStateErrorData G)
    (hreal :
      DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal D)
    (hid : G.determinantGroundStateIdentity)
    (hpro : G.prolateFourierConvergesToXi)
    {z : Complex}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ ErrorArbitrarilySmall E.error := by
  intro hsmall
  exact CCMGroundStateRoute.GroundStateProlateData.not_groundStateConvergesToProlate_of_nonrealRegularXiZero_and_rows
      G hreal hid hpro hz hzim (E.groundStateConvergesToProlate hsmall)

end GroundStateErrorData

/-- Packaged CCM ground-state error certificate. -/
structure GroundStateErrorRHCertificate where
  determinants : DeterminantHurwitzRoute.DeterminantApproximants.{u}
  data : CCMGroundStateRoute.GroundStateProlateData determinants
  errorData : GroundStateErrorData data
  allZerosReal :
    DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal determinants
  determinantGroundStateIdentity : data.determinantGroundStateIdentity
  errorArbitrarilySmall : ErrorArbitrarilySmall errorData.error
  prolateFourierConvergesToXi : data.prolateFourierConvergesToXi

namespace GroundStateErrorRHCertificate

/-- The packaged error data supplies the CCM ground-state rows. -/
theorem groundStateRows
    (cert : GroundStateErrorRHCertificate.{u}) :
    cert.data.GroundStateRows :=
  cert.errorData.groundStateRows_of_errorArbitrarilySmall
    cert.determinantGroundStateIdentity cert.errorArbitrarilySmall
    cert.prolateFourierConvergesToXi

/--
A packaged ground-state error certificate proves mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis
    (cert : GroundStateErrorRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.errorData.riemannHypothesis_of_errorArbitrarilySmall
    cert.allZerosReal cert.determinantGroundStateIdentity
    cert.errorArbitrarilySmall cert.prolateFourierConvergesToXi

end GroundStateErrorRHCertificate

/--
Packaged obstruction: with determinant real-zero data, determinant identity, and
prolate/Fourier convergence fixed, a non-real regular `Xi` zero forces the
ground-state error row to fail.
-/
structure GroundStateErrorFalsifier where
  determinants : DeterminantHurwitzRoute.DeterminantApproximants.{u}
  data : CCMGroundStateRoute.GroundStateProlateData determinants
  errorData : GroundStateErrorData data
  allZerosReal :
    DeterminantHurwitzRoute.DeterminantApproximants.AllZerosReal determinants
  determinantGroundStateIdentity : data.determinantGroundStateIdentity
  prolateFourierConvergesToXi : data.prolateFourierConvergesToXi
  badZero : Complex
  badZero_regular : RHReduction.riemannXiRegularZero badZero
  badZero_nonreal : badZero.im ≠ 0

namespace GroundStateErrorFalsifier

/-- The packaged obstruction refutes arbitrarily small ground-state error. -/
theorem not_errorArbitrarilySmall
    (cert : GroundStateErrorFalsifier.{u}) :
    ¬ ErrorArbitrarilySmall cert.errorData.error :=
  cert.errorData.not_errorArbitrarilySmall_of_nonrealRegularXiZero_and_rows
    cert.allZerosReal cert.determinantGroundStateIdentity
    cert.prolateFourierConvergesToXi cert.badZero_regular cert.badZero_nonreal

/-- The same non-real regular `Xi` zero refutes mathlib's RH directly. -/
theorem not_riemannHypothesis
    (cert : GroundStateErrorFalsifier.{u}) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact cert.badZero_nonreal
    ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      hRH cert.badZero cert.badZero_regular)

end GroundStateErrorFalsifier

/-- Packaged positive-floor obstruction for a proposed ground-state error budget. -/
structure GroundStateErrorFloorObstruction where
  determinants : DeterminantHurwitzRoute.DeterminantApproximants.{u}
  data : CCMGroundStateRoute.GroundStateProlateData determinants
  errorData : GroundStateErrorData data
  errorHasPositiveFloor : ErrorHasPositiveFloor errorData.error

namespace GroundStateErrorFloorObstruction

/-- A packaged positive floor blocks the arbitrarily-small-error row. -/
theorem not_errorArbitrarilySmall
    (obs : GroundStateErrorFloorObstruction.{u}) :
    ¬ ErrorArbitrarilySmall obs.errorData.error :=
  not_errorArbitrarilySmall_of_errorHasPositiveFloor obs.errorHasPositiveFloor

end GroundStateErrorFloorObstruction

end CCMGroundStateError
end JensenLadder
