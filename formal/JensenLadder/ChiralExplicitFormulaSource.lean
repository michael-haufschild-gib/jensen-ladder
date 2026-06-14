import JensenLadder.ChiralSourceTraceReconstruction
import JensenLadder.PrimeCepstrumHankelCarrier

/-!
# Chiral explicit-formula source gate

This module names the zero-blind completed explicit-formula source row for the
chiral prime-cepstrum/Hankel lane.

The previous source modules prove two finite same-carrier handoffs:

* `ChiralSourceMomentGate`: completed-source moments become Stieltjes-positive
  once they are identified with the same finite positive squared carrier;
* `ChiralSourceTraceReconstruction`: the completed-source trace fixes the
  finite Fredholm determinant on a connected zero-free domain once it is the
  same carrier trace and one basepoint is fixed.

This file adds the row that must precede both handoffs.  The completed explicit
formula source must be built without zero input from prime-power, archimedean,
and pole/normalization rows, and it must also be tied to the same carrier used
by the determinant.  Zero-blind source syntax alone is not enough.

It does not construct the explicit formula, the finite basis, the Hankel symbol,
fake-family tests, determinant convergence, or RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ChiralExplicitFormulaSource

universe u

/--
A zero-blind completed explicit-formula source package for the CPH carrier.

`sourceZeroBlind`, `vonMangoldtPrimePowerRow`, `archimedeanGammaRow`, and
`poleNormalizationRow` are the declared completed-source construction rows.
They are intentionally separated from `sourceSameCarrier`: the source may be
zero-blind and still fail to be the moment/trace source of the same determinant
carrier.
-/
structure ExplicitFormulaSourceCarrier where
  cphCarrier : PrimeCepstrumHankelCarrier.Carrier.{u}
  sourceTraceCarrier :
    ChiralSourceTraceReconstruction.FiniteSourceTraceCarrier.{u}
  sourceZeroBlind : Prop
  vonMangoldtPrimePowerRow : Prop
  archimedeanGammaRow : Prop
  poleNormalizationRow : Prop
  sourceSameCarrier : Prop
  noPostselectionFakeGate : Prop
  completedStream_of_sourceRows :
    sourceZeroBlind ->
      vonMangoldtPrimePowerRow ->
        archimedeanGammaRow ->
          poleNormalizationRow ->
            cphCarrier.completedSourceStream
  momentIdentity_of_sameCarrier :
    sourceSameCarrier ->
      sourceTraceCarrier.momentCarrier.sameCarrierMomentIdentity
  traceIdentity_of_sameCarrier :
    sourceSameCarrier ->
      sourceTraceCarrier.sameCarrierTraceIdentity
  cphMomentGate_of_sourceMoment :
    sourceTraceCarrier.momentCarrier.sameCarrierMomentIdentity ->
      cphCarrier.momentGate.sourceCarrierMomentIdentity
  nativeTraceRow_of_sourceTrace :
    sourceTraceCarrier.sameCarrierTraceIdentity ->
      cphCarrier.nativeLogDetTrace
  fakeFamilyRejection_of_noPostselection :
    noPostselectionFakeGate ->
      cphCarrier.fakeFamilyRejection

namespace ExplicitFormulaSourceCarrier

/-- The zero-blind completed-source construction rows. -/
structure CompletedSourceRows
    (E : ExplicitFormulaSourceCarrier.{u}) : Prop where
  zeroBlind : E.sourceZeroBlind
  primePowers : E.vonMangoldtPrimePowerRow
  archimedean : E.archimedeanGammaRow
  poleNormalization : E.poleNormalizationRow

/-- The live same-carrier row: the source must feed this determinant carrier. -/
def LiveSameCarrierRow (E : ExplicitFormulaSourceCarrier.{u}) : Prop :=
  E.sourceSameCarrier

/-- The finite structural CPH rows not supplied by source syntax alone. -/
structure StructuralRows
    (E : ExplicitFormulaSourceCarrier.{u}) : Prop where
  finiteWindowAndBasis : E.cphCarrier.finiteWindowAndBasis
  structuredHankelSymbol : E.cphCarrier.structuredHankelSymbol
  chiralCarrierConstruction : E.cphCarrier.chiralCarrierConstruction
  stieltjesMomentRows : E.cphCarrier.stieltjesMomentRows
  intrinsicAnomalyQuotient : E.cphCarrier.intrinsicAnomalyQuotient
  residualSchurSelector : E.cphCarrier.residualSchurSelector
  entireXiLimit : E.cphCarrier.entireXiLimit

/--
The full explicit-formula source rows required before the CPH carrier can be
consumed by the Fredholm-squared endpoint.
-/
structure FaithfulRows
    (E : ExplicitFormulaSourceCarrier.{u}) : Prop where
  completedSourceRows : E.CompletedSourceRows
  sameCarrierRow : E.LiveSameCarrierRow
  noPostselectionFakeGate : E.noPostselectionFakeGate
  structuralRows : E.StructuralRows

/-- Completed-source rows produce the CPH completed stream row. -/
theorem completedSourceStream_of_completedSourceRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.CompletedSourceRows) :
    E.cphCarrier.completedSourceStream :=
  E.completedStream_of_sourceRows
    h.zeroBlind h.primePowers h.archimedean h.poleNormalization

/-- Faithful explicit-source rows supply the source-to-Stieltjes certificate. -/
def sourceToStieltjesCertificate_of_faithfulRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.FaithfulRows) :
    ChiralSourceMomentGate.SourceToStieltjesCertificate.{u} where
  carrier := E.sourceTraceCarrier.momentCarrier
  sameCarrierMomentIdentity := E.momentIdentity_of_sameCarrier h.sameCarrierRow

/-- Faithful explicit-source rows supply the source-trace reconstruction certificate. -/
def sourceTraceReconstructionCertificate_of_faithfulRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.FaithfulRows) :
    ChiralSourceTraceReconstruction.SourceTraceReconstructionCertificate.{u} where
  carrier := E.sourceTraceCarrier
  sameCarrierTraceIdentity := E.traceIdentity_of_sameCarrier h.sameCarrierRow

/-- Faithful explicit-source rows supply the full CPH packet rows. -/
theorem cphRows_of_faithfulRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.FaithfulRows) :
    E.cphCarrier.CPHRows where
  finiteWindowAndBasis := h.structuralRows.finiteWindowAndBasis
  completedSourceStream :=
    E.completedSourceStream_of_completedSourceRows h.completedSourceRows
  structuredHankelSymbol := h.structuralRows.structuredHankelSymbol
  chiralCarrierConstruction := h.structuralRows.chiralCarrierConstruction
  nativeLogDetTrace :=
    E.nativeTraceRow_of_sourceTrace
      (E.traceIdentity_of_sameCarrier h.sameCarrierRow)
  stieltjesMomentRows := h.structuralRows.stieltjesMomentRows
  sourceCarrierMomentIdentity :=
    E.cphMomentGate_of_sourceMoment
      (E.momentIdentity_of_sameCarrier h.sameCarrierRow)
  intrinsicAnomalyQuotient := h.structuralRows.intrinsicAnomalyQuotient
  residualSchurSelector := h.structuralRows.residualSchurSelector
  fakeFamilyRejection :=
    E.fakeFamilyRejection_of_noPostselection h.noPostselectionFakeGate
  entireXiLimit := h.structuralRows.entireXiLimit

/-- Faithful explicit-source rows supply the existing Fredholm-squared rows. -/
theorem fredholmFaithfulRows_of_faithfulRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.FaithfulRows) :
    E.cphCarrier.fredholmCarrier.FaithfulRows :=
  E.cphCarrier.fredholmFaithfulRows_of_cphRows
    (E.cphRows_of_faithfulRows h)

/-- Faithful explicit-source rows prove mathlib's `RiemannHypothesis` conditionally. -/
theorem riemannHypothesis_of_faithfulRows
    (E : ExplicitFormulaSourceCarrier.{u})
    (h : E.FaithfulRows) :
    RiemannHypothesis :=
  E.cphCarrier.riemannHypothesis_of_cphRows
    (E.cphRows_of_faithfulRows h)

/-- A non-real regular `Xi` zero blocks faithful explicit-source rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (E : ExplicitFormulaSourceCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ E.FaithfulRows := by
  intro h
  exact E.cphCarrier.not_cphRows_of_nonrealRegularXiZero hz hzim
    (E.cphRows_of_faithfulRows h)

end ExplicitFormulaSourceCarrier

/-!
## Diagnostic-only calibration
-/

/--
A zero-blind-looking source package with no live same-carrier row.

This calibration object has prime-power, archimedean, and pole rows, but the
source is not tied to the same moment/trace carrier and the fake gate is absent.
-/
def diagnosticOnlySourceCarrier : ExplicitFormulaSourceCarrier.{0} where
  cphCarrier := PrimeCepstrumHankelCarrier.diagnosticOnlyCarrier
  sourceTraceCarrier :=
    ChiralSourceTraceReconstruction.FiniteSourceTraceCarrier.diagnosticOnly
  sourceZeroBlind := True
  vonMangoldtPrimePowerRow := True
  archimedeanGammaRow := True
  poleNormalizationRow := True
  sourceSameCarrier := False
  noPostselectionFakeGate := False
  completedStream_of_sourceRows := by
    intro _hzero _hprime _hgamma _hpole
    trivial
  momentIdentity_of_sameCarrier := by
    intro hfalse
    cases hfalse
  traceIdentity_of_sameCarrier := by
    intro hfalse
    cases hfalse
  cphMomentGate_of_sourceMoment := by
    intro hfalse
    cases hfalse
  nativeTraceRow_of_sourceTrace := by
    intro hfalse
    cases hfalse
  fakeFamilyRejection_of_noPostselection := by
    intro hfalse
    cases hfalse

/-- The diagnostic source carrier has all completed-source syntax rows. -/
theorem diagnosticOnlySourceCarrier_completedSourceRows :
    diagnosticOnlySourceCarrier.CompletedSourceRows :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Completed explicit-formula source syntax does not supply the live same-carrier row. -/
theorem completedSourceRows_do_not_supply_liveSameCarrierRow :
    ∃ E : ExplicitFormulaSourceCarrier.{0},
      E.CompletedSourceRows ∧ ¬ E.LiveSameCarrierRow :=
  ⟨diagnosticOnlySourceCarrier,
    diagnosticOnlySourceCarrier_completedSourceRows,
    by
      intro hfalse
      exact hfalse⟩

/-- Completed explicit-formula source syntax does not supply faithful CPH rows. -/
theorem completedSourceRows_do_not_supply_faithfulRows :
    ∃ E : ExplicitFormulaSourceCarrier.{0},
      E.CompletedSourceRows ∧ ¬ E.FaithfulRows :=
  ⟨diagnosticOnlySourceCarrier,
    diagnosticOnlySourceCarrier_completedSourceRows,
    by
      intro h
      exact h.sameCarrierRow⟩

/--
Completed source syntax alone does not supply a CPH carrier certificate.

The missing row here is not the explicit-formula syntax; it is the same-carrier
moment/trace and fake-gate package.
-/
theorem completedSourceRows_do_not_supply_cphRows :
    ∃ E : ExplicitFormulaSourceCarrier.{0},
      E.CompletedSourceRows ∧ ¬ E.cphCarrier.CPHRows :=
  ⟨diagnosticOnlySourceCarrier,
    diagnosticOnlySourceCarrier_completedSourceRows,
    by
      intro h
      exact h.sourceCarrierMomentIdentity⟩

/-- Existence of a faithful zero-blind explicit-formula source carrier. -/
def HasFaithfulExplicitFormulaSourceCarrier : Prop :=
  ∃ E : ExplicitFormulaSourceCarrier.{u}, E.FaithfulRows

/-- A faithful explicit-formula source carrier supplies the existing CPH carrier. -/
theorem hasFaithfulPrimeCepstrumHankelCarrier_of_hasFaithfulExplicitFormulaSourceCarrier
    (hE : HasFaithfulExplicitFormulaSourceCarrier.{u}) :
    PrimeCepstrumHankelCarrier.HasFaithfulPrimeCepstrumHankelCarrier.{u} := by
  rcases hE with ⟨E, hrows⟩
  exact ⟨E.cphCarrier, E.cphRows_of_faithfulRows hrows⟩

/-- A faithful explicit-formula source carrier proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_hasFaithfulExplicitFormulaSourceCarrier
    (hE : HasFaithfulExplicitFormulaSourceCarrier.{u}) :
    RiemannHypothesis := by
  rcases hE with ⟨E, hrows⟩
  exact E.riemannHypothesis_of_faithfulRows hrows

/-- A non-real regular `Xi` zero rules out faithful explicit-formula source carriers. -/
theorem not_hasFaithfulExplicitFormulaSourceCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulExplicitFormulaSourceCarrier.{u} := by
  rintro ⟨E, hrows⟩
  exact E.not_faithfulRows_of_nonrealRegularXiZero hz hzim hrows

/-- Packaged conditional RH certificate for the explicit-formula source route. -/
structure ExplicitFormulaSourceRHCertificate where
  carrier : ExplicitFormulaSourceCarrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace ExplicitFormulaSourceRHCertificate

/-- The packaged explicit-formula source certificate supplies CPH rows. -/
theorem cphRows
    (cert : ExplicitFormulaSourceRHCertificate.{u}) :
    cert.carrier.cphCarrier.CPHRows :=
  cert.carrier.cphRows_of_faithfulRows cert.faithfulRows

/-- The packaged explicit-formula source certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : ExplicitFormulaSourceRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.carrier.riemannHypothesis_of_faithfulRows cert.faithfulRows

end ExplicitFormulaSourceRHCertificate

end ChiralExplicitFormulaSource
end JensenLadder
