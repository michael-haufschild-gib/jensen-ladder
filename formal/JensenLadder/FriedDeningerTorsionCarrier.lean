import JensenLadder.DeningerFlowUnitary

/-!
# Fried-Deninger torsion carrier boundary

This module records the Lean-facing boundary behind the current
Fried/Deninger torsion discussion.

The important split is the torsion-form metric dichotomy:

* a weak spectral determinant identity can be zero-blind and RH-agnostic, but it
  is not yet a genuine Fried/Cheeger--Muller torsion theorem;
* genuine analytic torsion requires a metric; to feed the existing Deninger
  flow endpoint, that metric must supply the positive/polarized reality rows
  and the determinant target must be selected without an eta-phase anomaly.

This module does not construct Deninger's cohomology, prove a Fried theorem,
prove Cheeger--Muller, build the determinant line, cancel an eta phase, prove a
polarization, or prove RH.

Evidence class: formal/certificate artifact; theorem-target refinement;
dead-end-boundary calibration.  Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

namespace JensenLadder
namespace FriedDeningerTorsionCarrier

universe u

/--
A Fried/Deninger torsion carrier candidate.

`flowCarrier` is the already-formalized Deninger flow endpoint.  The remaining
fields separate the weak determinant identity rows from the genuine torsion and
positive-metric rows needed to feed that endpoint.
-/
structure Carrier where
  flowCarrier : DeningerFlowUnitary.FlowCarrier.{u}
  sourceNativeSpecZ : Prop
  primeOrbitTraceFormula : Prop
  friedCheegerMullerTorsion : Prop
  torsionMetricChosen : Prop
  positivePolarizationMetric : Prop
  holomorphicDeterminantPromotion : Prop
  targetSelectorXi : Prop
  etaPhaseCancelled : Prop
  fakeFamilyRejection : Prop
  polarizedCohomology_of_positiveMetric :
    positivePolarizationMetric -> flowCarrier.polarizedCohomology
  normalizedFlowUnitary_of_positiveMetric :
    positivePolarizationMetric -> flowCarrier.normalizedFlowUnitary
  spectralRegularity_of_determinantPromotion :
    holomorphicDeterminantPromotion ->
      targetSelectorXi ->
        flowCarrier.spectralRegularity
  determinantIdentity_of_torsionTarget :
    sourceNativeSpecZ ->
      primeOrbitTraceFormula ->
        friedCheegerMullerTorsion ->
          torsionMetricChosen ->
            holomorphicDeterminantPromotion ->
              targetSelectorXi ->
                etaPhaseCancelled ->
                  flowCarrier.determinantIdentity

namespace Carrier

/-- Weak RH-agnostic determinant rows, without genuine torsion or positivity. -/
structure WeakDeterminantRows (C : Carrier.{u}) : Prop where
  sourceNativeSpecZ : C.sourceNativeSpecZ
  primeOrbitTraceFormula : C.primeOrbitTraceFormula
  holomorphicDeterminantPromotion : C.holomorphicDeterminantPromotion
  targetSelectorXi : C.targetSelectorXi

/-- Genuine Fried/Cheeger--Muller torsion rows: torsion needs a metric. -/
structure GenuineTorsionRows (C : Carrier.{u}) : Prop where
  friedCheegerMullerTorsion : C.friedCheegerMullerTorsion
  torsionMetricChosen : C.torsionMetricChosen

/-- Positive/polarized metric rows, including cancellation of the eta phase. -/
structure PositiveMetricRows (C : Carrier.{u}) : Prop where
  positivePolarizationMetric : C.positivePolarizationMetric
  etaPhaseCancelled : C.etaPhaseCancelled

/--
Full rows required before the Fried/Deninger torsion carrier can be consumed by
the existing flow-unitarity endpoint.
-/
structure FaithfulRows (C : Carrier.{u}) : Prop where
  weakDeterminantRows : C.WeakDeterminantRows
  genuineTorsionRows : C.GenuineTorsionRows
  positiveMetricRows : C.PositiveMetricRows
  fakeFamilyRejection : C.fakeFamilyRejection

/-- Full torsion rows supply the Deninger flow-reality rows. -/
theorem flowRealityRows_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.flowCarrier.RealityRows :=
  ⟨C.polarizedCohomology_of_positiveMetric
      h.positiveMetricRows.positivePolarizationMetric,
    C.normalizedFlowUnitary_of_positiveMetric
      h.positiveMetricRows.positivePolarizationMetric,
    C.spectralRegularity_of_determinantPromotion
      h.weakDeterminantRows.holomorphicDeterminantPromotion
      h.weakDeterminantRows.targetSelectorXi⟩

/-- Full torsion rows supply the Deninger flow determinant row. -/
theorem determinantIdentity_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.flowCarrier.determinantIdentity :=
  C.determinantIdentity_of_torsionTarget
    h.weakDeterminantRows.sourceNativeSpecZ
    h.weakDeterminantRows.primeOrbitTraceFormula
    h.genuineTorsionRows.friedCheegerMullerTorsion
    h.genuineTorsionRows.torsionMetricChosen
    h.weakDeterminantRows.holomorphicDeterminantPromotion
    h.weakDeterminantRows.targetSelectorXi
    h.positiveMetricRows.etaPhaseCancelled

/-- Full torsion rows supply the existing Deninger flow endpoint rows. -/
theorem flowFaithfulRows_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.flowCarrier.FaithfulRows :=
  ⟨C.flowRealityRows_of_faithfulRows h,
    C.determinantIdentity_of_faithfulRows h⟩

/-- Full Fried/Deninger torsion rows prove mathlib's RH conditionally. -/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  C.flowCarrier.riemannHypothesis_of_faithfulRows
    (C.flowFaithfulRows_of_faithfulRows h)

/-- A non-real regular `Xi` zero blocks faithful torsion rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows := by
  intro h
  exact C.flowCarrier.not_faithfulRows_of_nonrealRegularXiZero hz hzim
    (C.flowFaithfulRows_of_faithfulRows h)

end Carrier

/-!
## Calibration carriers
-/

/--
A weak determinant identity carrier with no genuine torsion or positive metric.

This models the RH-agnostic spectral determinant fork: source/trace/determinant
syntax alone is not a Fried/Cheeger--Muller torsion handoff.
-/
def weakOnlyCarrier : Carrier.{0} where
  flowCarrier := _root_.JensenLadder.DeningerFlowUnitary.emptyRealityFlowCarrier
  sourceNativeSpecZ := True
  primeOrbitTraceFormula := True
  friedCheegerMullerTorsion := False
  torsionMetricChosen := False
  positivePolarizationMetric := False
  holomorphicDeterminantPromotion := True
  targetSelectorXi := True
  etaPhaseCancelled := False
  fakeFamilyRejection := False
  polarizedCohomology_of_positiveMetric := by
    intro hfalse
    cases hfalse
  normalizedFlowUnitary_of_positiveMetric := by
    intro hfalse
    cases hfalse
  spectralRegularity_of_determinantPromotion := by
    intro _hdet _htarget
    trivial
  determinantIdentity_of_torsionTarget := by
    intro _hsource _htrace htorsion
    cases htorsion

/-- The weak-only carrier satisfies the weak determinant rows. -/
theorem weakOnlyCarrier_weakDeterminantRows :
    weakOnlyCarrier.WeakDeterminantRows :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Weak determinant rows alone do not supply faithful torsion rows. -/
theorem weakDeterminantRows_do_not_supply_faithfulRows :
    ∃ C : Carrier.{0}, C.WeakDeterminantRows ∧ ¬ C.FaithfulRows :=
  ⟨weakOnlyCarrier, weakOnlyCarrier_weakDeterminantRows, by
    intro h
    exact h.genuineTorsionRows.friedCheegerMullerTorsion⟩

/--
A genuine-torsion-looking carrier with a chosen metric, but no positive
polarization or eta-phase cancellation.
-/
def torsionMetricOnlyCarrier : Carrier.{0} where
  flowCarrier := _root_.JensenLadder.DeningerFlowUnitary.emptyRealityFlowCarrier
  sourceNativeSpecZ := True
  primeOrbitTraceFormula := True
  friedCheegerMullerTorsion := True
  torsionMetricChosen := True
  positivePolarizationMetric := False
  holomorphicDeterminantPromotion := True
  targetSelectorXi := True
  etaPhaseCancelled := False
  fakeFamilyRejection := True
  polarizedCohomology_of_positiveMetric := by
    intro hfalse
    cases hfalse
  normalizedFlowUnitary_of_positiveMetric := by
    intro hfalse
    cases hfalse
  spectralRegularity_of_determinantPromotion := by
    intro _hdet _htarget
    trivial
  determinantIdentity_of_torsionTarget := by
    intro _hsource _htrace _htorsion _hmetric _hdet _htarget heta
    cases heta

/-- The torsion-metric-only carrier satisfies the genuine torsion rows. -/
theorem torsionMetricOnlyCarrier_genuineTorsionRows :
    torsionMetricOnlyCarrier.GenuineTorsionRows :=
  ⟨trivial, trivial⟩

/-- Genuine torsion rows alone do not supply the positive/polarized metric rows. -/
theorem genuineTorsionRows_do_not_supply_positiveMetricRows :
    ∃ C : Carrier.{0}, C.GenuineTorsionRows ∧ ¬ C.PositiveMetricRows :=
  ⟨torsionMetricOnlyCarrier, torsionMetricOnlyCarrier_genuineTorsionRows, by
    intro h
    exact h.positivePolarizationMetric⟩

/--
A positive-metric-looking carrier with no target selector or determinant
promotion.
-/
def positiveMetricOnlyCarrier : Carrier.{0} where
  flowCarrier := _root_.JensenLadder.DeningerFlowUnitary.emptyRealityFlowCarrier
  sourceNativeSpecZ := True
  primeOrbitTraceFormula := True
  friedCheegerMullerTorsion := True
  torsionMetricChosen := True
  positivePolarizationMetric := True
  holomorphicDeterminantPromotion := False
  targetSelectorXi := False
  etaPhaseCancelled := True
  fakeFamilyRejection := True
  polarizedCohomology_of_positiveMetric := by
    intro _hpositive
    trivial
  normalizedFlowUnitary_of_positiveMetric := by
    intro _hpositive
    trivial
  spectralRegularity_of_determinantPromotion := by
    intro hfalse
    cases hfalse
  determinantIdentity_of_torsionTarget := by
    intro _hsource _htrace _htorsion _hmetric hdet
    cases hdet

/-- The positive-metric-only carrier satisfies the positive metric rows. -/
theorem positiveMetricOnlyCarrier_positiveMetricRows :
    positiveMetricOnlyCarrier.PositiveMetricRows :=
  ⟨trivial, trivial⟩

/-- Positive metric rows alone do not supply faithful torsion rows. -/
theorem positiveMetricRows_do_not_supply_faithfulRows :
    ∃ C : Carrier.{0}, C.PositiveMetricRows ∧ ¬ C.FaithfulRows :=
  ⟨positiveMetricOnlyCarrier, positiveMetricOnlyCarrier_positiveMetricRows, by
    intro h
    exact h.weakDeterminantRows.holomorphicDeterminantPromotion⟩

/-- Existence of a faithful Fried/Deninger torsion carrier. -/
def HasFaithfulFriedDeningerTorsionCarrier : Prop :=
  ∃ C : Carrier.{u}, C.FaithfulRows

/-- A faithful Fried/Deninger torsion carrier supplies the Deninger flow carrier. -/
theorem hasFaithfulDeningerFlowCarrier_of_hasFaithfulFriedDeningerTorsionCarrier
    (hC : HasFaithfulFriedDeningerTorsionCarrier.{u}) :
    DeningerFlowUnitary.HasFaithfulDeningerFlowCarrier.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.flowCarrier, C.flowFaithfulRows_of_faithfulRows hrows⟩

/-- A faithful Fried/Deninger torsion carrier proves mathlib's RH conditionally. -/
theorem riemannHypothesis_of_hasFaithfulFriedDeningerTorsionCarrier
    (hC : HasFaithfulFriedDeningerTorsionCarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_faithfulRows hrows

/-- A non-real regular `Xi` zero rules out faithful torsion carriers. -/
theorem not_hasFaithfulFriedDeningerTorsionCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulFriedDeningerTorsionCarrier.{u} := by
  rintro ⟨C, hrows⟩
  exact C.not_faithfulRows_of_nonrealRegularXiZero hz hzim hrows

/-- Packaged conditional RH certificate for the Fried/Deninger torsion route. -/
structure FriedDeningerTorsionRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace FriedDeningerTorsionRHCertificate

/-- The packaged torsion certificate supplies Deninger flow rows. -/
theorem flowFaithfulRows
    (cert : FriedDeningerTorsionRHCertificate.{u}) :
    cert.carrier.flowCarrier.FaithfulRows :=
  cert.carrier.flowFaithfulRows_of_faithfulRows cert.faithfulRows

/-- The packaged torsion certificate proves mathlib's RH conditionally. -/
theorem riemannHypothesis
    (cert : FriedDeningerTorsionRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.carrier.riemannHypothesis_of_faithfulRows cert.faithfulRows

end FriedDeningerTorsionRHCertificate

end FriedDeningerTorsionCarrier
end JensenLadder
