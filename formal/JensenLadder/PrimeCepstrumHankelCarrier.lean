import JensenLadder.FredholmSquaredCarrier

/-!
# Prime-cepstrum Hankel carrier boundary

This module records the Lean-facing boundary for the current
`PrimeCepstrumHankelCarrier` packet.

The packet tries to turn the completed explicit-formula stream into a
zero-blind Toeplitz/Hankel/Gramian symbol, then into a chiral positive squared
carrier `A = T*T`, and finally into the ordinary Fredholm squared determinant
already consumed by `FredholmSquaredCarrier`.

The important separation is the source-to-moment gate:

* zero-side moments and `Xi` Taylor moments are diagnostics;
* the live proof row is the same-carrier identity producing the moments from
  the completed explicit-formula source stream;
* Stieltjes/Hankel positivity alone is still not the determinant identity or
  fake-family separation.

This file does not construct the finite basis, source stream, Hankel symbol,
chiral carrier, Stieltjes measure, anomaly quotient, residual selector, fake
gate, determinant convergence, or RH.  It names the rows and proves the exact
handoff to the existing Fredholm-squared endpoint.

Evidence class: theorem-target refinement / formal certificate.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace PrimeCepstrumHankelCarrier

universe u

/--
The source-to-moment gate for the chiral/Hankel packet.

The first two rows are valid diagnostics but circular or target-side as proof
input.  The third row is the live carrier row: the moments must be produced by
the same completed-source carrier whose determinant is later consumed.
-/
structure MomentSourceGate where
  zeroSideMomentDiagnostics : Prop
  xiTaylorMomentDiagnostics : Prop
  sourceCarrierMomentIdentity : Prop

namespace MomentSourceGate

/-- Diagnostic moment rows: useful for screening, not a proof source. -/
def DiagnosticRows (G : MomentSourceGate) : Prop :=
  G.zeroSideMomentDiagnostics ∧ G.xiTaylorMomentDiagnostics

/-- The live source-carrier moment row. -/
def LiveRow (G : MomentSourceGate) : Prop :=
  G.sourceCarrierMomentIdentity

/-- A gate with diagnostic rows but no live source-carrier identity. -/
def diagnosticOnly : MomentSourceGate where
  zeroSideMomentDiagnostics := True
  xiTaylorMomentDiagnostics := True
  sourceCarrierMomentIdentity := False

/-- Diagnostic zero-side/`Xi`-side moments do not supply the live source row. -/
theorem diagnosticRows_do_not_supply_liveRow :
    ∃ G : MomentSourceGate, G.DiagnosticRows ∧ ¬ G.LiveRow :=
  ⟨diagnosticOnly, ⟨trivial, trivial⟩, by
    intro hfalse
    exact hfalse⟩

end MomentSourceGate

/--
Prime-cepstrum/Hankel carrier candidate.

The rows follow the packet CPH-0 through CPH-9.  Adapter fields say how these
rows would supply the existing Fredholm-squared carrier rows.  This keeps the
consumer exact while leaving the real carrier construction explicit.
-/
structure Carrier where
  SourceStream : Type u
  Symbol : Type u
  FakeStream : Type u
  fredholmCarrier : FredholmSquaredCarrier.Carrier.{u}
  momentGate : MomentSourceGate
  finiteWindowAndBasis : Prop
  completedSourceStream : Prop
  structuredHankelSymbol : Prop
  chiralCarrierConstruction : Prop
  nativeLogDetTrace : Prop
  stieltjesMomentRows : Prop
  intrinsicAnomalyQuotient : Prop
  residualSchurSelector : Prop
  fakeFamilyRejection : Prop
  entireXiLimit : Prop
  positiveSquare_of_chiralCarrier :
    chiralCarrierConstruction -> fredholmCarrier.positiveSquare
  traceClassSquare_of_stieltjes :
    stieltjesMomentRows -> fredholmCarrier.traceClassSquare
  hilbertSchmidtRoot_of_chiralCarrier :
    chiralCarrierConstruction -> fredholmCarrier.hilbertSchmidtRoot
  determinantIdentity_of_cphRows :
    finiteWindowAndBasis ->
      completedSourceStream ->
        structuredHankelSymbol ->
          nativeLogDetTrace ->
            momentGate.sourceCarrierMomentIdentity ->
              intrinsicAnomalyQuotient ->
                residualSchurSelector ->
                  fakeFamilyRejection ->
                    entireXiLimit ->
                      fredholmCarrier.fredholmDeterminantIdentity

namespace Carrier

/-- The full CPH packet rows required before Fredholm-squared consumption. -/
structure CPHRows (C : Carrier.{u}) : Prop where
  finiteWindowAndBasis : C.finiteWindowAndBasis
  completedSourceStream : C.completedSourceStream
  structuredHankelSymbol : C.structuredHankelSymbol
  chiralCarrierConstruction : C.chiralCarrierConstruction
  nativeLogDetTrace : C.nativeLogDetTrace
  stieltjesMomentRows : C.stieltjesMomentRows
  sourceCarrierMomentIdentity : C.momentGate.sourceCarrierMomentIdentity
  intrinsicAnomalyQuotient : C.intrinsicAnomalyQuotient
  residualSchurSelector : C.residualSchurSelector
  fakeFamilyRejection : C.fakeFamilyRejection
  entireXiLimit : C.entireXiLimit

/-- Full CPH rows supply the existing ordinary Fredholm squared rows. -/
theorem fredholmFaithfulRows_of_cphRows
    (C : Carrier.{u})
    (h : C.CPHRows) :
    C.fredholmCarrier.FaithfulRows :=
  ⟨C.positiveSquare_of_chiralCarrier h.chiralCarrierConstruction,
    C.traceClassSquare_of_stieltjes h.stieltjesMomentRows,
    C.hilbertSchmidtRoot_of_chiralCarrier h.chiralCarrierConstruction,
    C.determinantIdentity_of_cphRows
      h.finiteWindowAndBasis
      h.completedSourceStream
      h.structuredHankelSymbol
      h.nativeLogDetTrace
      h.sourceCarrierMomentIdentity
      h.intrinsicAnomalyQuotient
      h.residualSchurSelector
      h.fakeFamilyRejection
      h.entireXiLimit⟩

/-- Full CPH rows prove mathlib's `RiemannHypothesis` conditionally. -/
theorem riemannHypothesis_of_cphRows
    (C : Carrier.{u})
    (h : C.CPHRows) :
    RiemannHypothesis :=
  C.fredholmCarrier.riemannHypothesis_of_faithfulRows
    (C.fredholmFaithfulRows_of_cphRows h)

/-- A non-real regular `Xi` zero blocks full CPH rows. -/
theorem not_cphRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.CPHRows := by
  intro h
  exact C.fredholmCarrier.not_faithfulRows_of_nonrealRegularXiZero hz hzim
    (C.fredholmFaithfulRows_of_cphRows h)

end Carrier

/-!
## Diagnostic-only calibration

The next carrier is intentionally empty and diagnostic-only.  It shows that
moment diagnostics and Stieltjes-looking rows do not by themselves provide the
source-carrier identity, fake rejection, or determinant convergence.
-/

/-- A diagnostic-only CPH carrier with no live source moment row. -/
def diagnosticOnlyCarrier : Carrier.{0} where
  SourceStream := PUnit
  Symbol := PUnit
  FakeStream := PUnit
  fredholmCarrier := {
    Spectrum := Empty
    energy := fun γ => nomatch γ
    positiveSquare := True
    traceClassSquare := True
    hilbertSchmidtRoot := True
    fredholmDeterminantIdentity := False
    nonnegative_of_positiveSquare := by
      intro _hpos γ
      cases γ
    complete_of_fredholmRows := by
      intro _htrace _hroot hfalse
      cases hfalse
  }
  momentGate := MomentSourceGate.diagnosticOnly
  finiteWindowAndBasis := True
  completedSourceStream := True
  structuredHankelSymbol := True
  chiralCarrierConstruction := True
  nativeLogDetTrace := True
  stieltjesMomentRows := True
  intrinsicAnomalyQuotient := True
  residualSchurSelector := True
  fakeFamilyRejection := False
  entireXiLimit := False
  positiveSquare_of_chiralCarrier := by
    intro _h
    trivial
  traceClassSquare_of_stieltjes := by
    intro _h
    trivial
  hilbertSchmidtRoot_of_chiralCarrier := by
    intro _h
    trivial
  determinantIdentity_of_cphRows := by
    intro _hwin _hsource _hsymbol _htrace hmoment
    cases hmoment

/--
Diagnostic source moments and Stieltjes-looking rows do not supply the full CPH
packet.
-/
theorem diagnosticMomentRows_do_not_supply_cphRows :
    ∃ C : Carrier.{0},
      C.momentGate.DiagnosticRows ∧ C.stieltjesMomentRows ∧ ¬ C.CPHRows := by
  refine ⟨diagnosticOnlyCarrier, ?_, trivial, ?_⟩
  · exact ⟨trivial, trivial⟩
  · intro h
    exact h.sourceCarrierMomentIdentity

/-- Stieltjes rows alone do not supply the Fredholm determinant identity. -/
theorem stieltjesRows_do_not_supply_determinantIdentity :
    ∃ C : Carrier.{0},
      C.stieltjesMomentRows ∧ ¬ C.fredholmCarrier.fredholmDeterminantIdentity := by
  refine ⟨diagnosticOnlyCarrier, trivial, ?_⟩
  intro hfalse
  exact hfalse

/-- Existence of a faithful prime-cepstrum/Hankel carrier. -/
def HasFaithfulPrimeCepstrumHankelCarrier : Prop :=
  ∃ C : Carrier.{u}, C.CPHRows

/-- A faithful CPH carrier supplies the Fredholm-squared endpoint. -/
theorem hasFaithfulFredholmSquaredCarrier_of_hasFaithfulPrimeCepstrumHankelCarrier
    (hC : HasFaithfulPrimeCepstrumHankelCarrier.{u}) :
    FredholmSquaredCarrier.HasFaithfulFredholmSquaredCarrier.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.fredholmCarrier, C.fredholmFaithfulRows_of_cphRows hrows⟩

/-- A faithful CPH carrier proves mathlib's `RiemannHypothesis` conditionally. -/
theorem riemannHypothesis_of_hasFaithfulPrimeCepstrumHankelCarrier
    (hC : HasFaithfulPrimeCepstrumHankelCarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_cphRows hrows

/-- A non-real regular `Xi` zero rules out every faithful CPH carrier. -/
theorem not_hasFaithfulPrimeCepstrumHankelCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulPrimeCepstrumHankelCarrier.{u} := by
  rintro ⟨C, hrows⟩
  exact C.not_cphRows_of_nonrealRegularXiZero hz hzim hrows

/-- Packaged conditional certificate for the CPH route. -/
structure PrimeCepstrumHankelRHCertificate where
  carrier : Carrier.{u}
  cphRows : carrier.CPHRows

namespace PrimeCepstrumHankelRHCertificate

/-- The packaged CPH certificate supplies the existing Fredholm-squared rows. -/
theorem fredholmFaithfulRows
    (cert : PrimeCepstrumHankelRHCertificate.{u}) :
    cert.carrier.fredholmCarrier.FaithfulRows :=
  cert.carrier.fredholmFaithfulRows_of_cphRows cert.cphRows

/-- The packaged CPH certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : PrimeCepstrumHankelRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.carrier.riemannHypothesis_of_cphRows cert.cphRows

end PrimeCepstrumHankelRHCertificate

end PrimeCepstrumHankelCarrier
end JensenLadder
