import JensenLadder.RHReduction

/-!
# Connes--van Suijlekom spectral-route handoff

This module records the Lean-facing interface for the current CCM/C-vS
spectral route.

The route has three logically distinct rows:

* finite approximants attached to a semilocal Weil/prolate operator;
* a Connes--van Suijlekom style engine turning simple even bottom states into
  real-zero finite approximants;
* a Hurwitz/convergence row transferring those finite real-zero approximants to
  the regular `Xi` zero set.

Only the third row can carry the limiting RH content.  The first two rows, even
when supplied, do not prove convergence to `Xi`; the convergence row is the
load-bearing spectral-identification theorem.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CVSSpectralRoute

universe u

/-- A family of finite-scale entire-function approximants.  The analytic facts
that these are entire functions and arise from a semilocal operator are kept
outside this finite interface; this structure only carries the zero predicate
needed by the RH handoff. -/
structure FiniteScaleApproximants where
  Scale : Type u
  approximant : Scale → ℂ → ℂ

/-- Every zero of every finite approximant is real. -/
def AllApproximantZerosReal (A : FiniteScaleApproximants.{u}) : Prop :=
  ∀ a : A.Scale, ∀ z : ℂ, A.approximant a z = 0 → z.im = 0

/-- Bottom-state simplicity and evenness data, together with the C-vS real-zero
engine for the finite approximants.

Supplying this for a concrete operator family is not an RH proof: it only proves
real zeros for the finite approximants.  The limiting convergence to `Xi` is a
separate row below. -/
structure SimpleEvenGroundStateData (A : FiniteScaleApproximants.{u}) where
  simpleBottom : A.Scale → Prop
  evenGroundState : A.Scale → Prop
  cvs_realZeros_of_simple_even :
    (∀ a : A.Scale, simpleBottom a ∧ evenGroundState a) →
      AllApproximantZerosReal A

/-- The finite C-vS hypothesis: every scale has a simple even bottom state. -/
def SimpleEvenGroundStates {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A) : Prop :=
  ∀ a : A.Scale, G.simpleBottom a ∧ G.evenGroundState a

/-- The Hurwitz/convergence row for transferring finite approximant
real-rootedness to regular `Xi` zeros.

The predicate `convergesToXi` is deliberately abstract: in the CCM/Suzuki route
it stands for the local-uniform spectral convergence theorem.  That theorem is
the open spectral-identification row; this structure does not prove it. -/
structure HurwitzXiConvergence (A : FiniteScaleApproximants.{u}) where
  convergesToXi : Prop
  regularXiZerosReal_of_approximantsReal_and_convergence :
    AllApproximantZerosReal A → convergesToXi →
      ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0

/-- The C-vS spectral route proves RH once the finite simple-even row and the
Hurwitz/convergence row are both supplied. -/
theorem riemannHypothesis_of_simpleEvenGroundStates_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (hsimpleEven : SimpleEvenGroundStates G)
    (hconv : H.convergesToXi) :
    RiemannHypothesis := by
  exact (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (H.regularXiZerosReal_of_approximantsReal_and_convergence
      (G.cvs_realZeros_of_simple_even hsimpleEven) hconv)

/-- A non-real regular `Xi` zero rules out convergence if all finite
approximants have real zeros. -/
theorem not_convergence_of_nonrealRegularXiZero_and_approximantsReal
    {A : FiniteScaleApproximants.{u}}
    (H : HurwitzXiConvergence A)
    (hreal : AllApproximantZerosReal A)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ H.convergesToXi := by
  intro hconv
  exact hzim
    (H.regularXiZerosReal_of_approximantsReal_and_convergence hreal hconv z hz)

/-- A non-real regular `Xi` zero rules out the C-vS convergence row whenever the
finite simple-even row is present. -/
theorem not_convergence_of_nonrealRegularXiZero_and_simpleEvenGroundStates
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (hsimpleEven : SimpleEvenGroundStates G)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ H.convergesToXi :=
  not_convergence_of_nonrealRegularXiZero_and_approximantsReal H
    (G.cvs_realZeros_of_simple_even hsimpleEven) hz hzim

/-- Conversely, under the Hurwitz/convergence row, a non-real regular `Xi` zero
rules out the finite simple-even C-vS hypothesis. -/
theorem not_simpleEvenGroundStates_of_nonrealRegularXiZero_and_convergence
    {A : FiniteScaleApproximants.{u}}
    (G : SimpleEvenGroundStateData A)
    (H : HurwitzXiConvergence A)
    (hconv : H.convergesToXi)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ SimpleEvenGroundStates G := by
  intro hsimpleEven
  exact not_convergence_of_nonrealRegularXiZero_and_simpleEvenGroundStates
    G H hsimpleEven hz hzim hconv

/-- Packaged certificate for the C-vS spectral route.  The certificate is only
as strong as its convergence field: finite simple-even data alone is
insufficient. -/
structure CVSSpectralRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  simpleEvenGroundStates : SimpleEvenGroundStates groundStateData
  convergesToXi : convergence.convergesToXi

namespace CVSSpectralRHCertificate

/-- A packaged C-vS spectral certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : CVSSpectralRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence
    cert.groundStateData cert.convergence
    cert.simpleEvenGroundStates cert.convergesToXi

end CVSSpectralRHCertificate

/-- Packaged obstruction for the C-vS route: under the same convergence row, a
non-real regular `Xi` zero falsifies the finite simple-even hypothesis. -/
structure CVSSpectralFalsifier where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  convergence : HurwitzXiConvergence approximants
  convergesToXi : convergence.convergesToXi
  badZero : ℂ
  badZero_regular : RHReduction.riemannXiRegularZero badZero
  badZero_nonreal : badZero.im ≠ 0

namespace CVSSpectralFalsifier

/-- A packaged C-vS obstruction rules out the finite simple-even hypothesis for
the supplied approximant family. -/
theorem not_simpleEvenGroundStates
    (cert : CVSSpectralFalsifier.{u}) :
    ¬ SimpleEvenGroundStates cert.groundStateData :=
  not_simpleEvenGroundStates_of_nonrealRegularXiZero_and_convergence
    cert.groundStateData cert.convergence cert.convergesToXi
    cert.badZero_regular cert.badZero_nonreal

/-- The same packaged obstruction refutes mathlib's RH directly. -/
theorem not_riemannHypothesis
    (cert : CVSSpectralFalsifier.{u}) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact cert.badZero_nonreal
    ((RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
      hRH cert.badZero cert.badZero_regular)

end CVSSpectralFalsifier

end CVSSpectralRoute
end JensenLadder
