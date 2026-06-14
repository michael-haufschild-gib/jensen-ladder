import JensenLadder.ChiralExplicitFormulaSource
import JensenLadder.SchurStarAssemblyCarrier
import JensenLadder.AbsoluteBudgetFakeFamilyBlindness

/-!
# Euler-loaded primitive projection gate

This module packages the finite theorem socket suggested by the current
same-carrier search: a source-built finite star algebra, a primitive projection,
and a Schur square/projection residual are not enough.  The row must also be
Euler-loaded and fake-resistant before it may discharge the
`noPostselectionFakeGate` required by `ChiralExplicitFormulaSource`.

The module therefore records two facts:

* Schur square/projection syntax is a useful finite algebra row, but by itself
  it is fake-blind under unit response twists.
* A fully Euler-loaded primitive projection package hands off to the existing
  explicit-formula source carrier and hence to the CPH/Fredholm endpoint.

It does not construct the finite algebra, prove the Euler/archimedean
coherence theorem, prove adversarial tail bounds, prove fake-family failure, or
prove RH.

Evidence class: formal/certificate artifact; theorem-target refinement;
fake-gate boundary.  Theorem M is proven, but Theorem M does not prove RH by
itself.
-/

namespace JensenLadder
namespace EulerLoadedPrimitiveProjection

universe u

/--
Rows in the finite Euler-loaded primitive projection certificate.

The first three rows are finite algebra/syntax rows.  The remaining four rows
are the load-bearing arithmetic and fake-gate rows that prevent a Schur
certificate from being merely absolute-budget/fake-blind.
-/
structure PrimitiveProjectionRows where
  sourceBuiltFiniteStarAlgebra : Prop
  primitiveProjection : Prop
  schurStarSquareProjection : Prop
  eulerArchimedeanCoherence : Prop
  adversarialTailBound : Prop
  noPostselectionSelector : Prop
  fakeFamilyFailure : Prop

namespace PrimitiveProjectionRows

/-- The finite Schur/projection syntax rows. -/
def SchurSyntaxRows (R : PrimitiveProjectionRows) : Prop :=
  R.sourceBuiltFiniteStarAlgebra ∧
    R.primitiveProjection ∧
      R.schurStarSquareProjection

/-- The arithmetic and fake-gate rows that make the projection zeta-specific. -/
def EulerLoadedRows (R : PrimitiveProjectionRows) : Prop :=
  R.eulerArchimedeanCoherence ∧
    R.adversarialTailBound ∧
      R.noPostselectionSelector ∧
        R.fakeFamilyFailure

/-- Full primitive-projection rows. -/
def Holds (R : PrimitiveProjectionRows) : Prop :=
  R.SchurSyntaxRows ∧ R.EulerLoadedRows

/-- A Schur/projection-only row package with no Euler load or fake gate. -/
def schurOnly : PrimitiveProjectionRows where
  sourceBuiltFiniteStarAlgebra := True
  primitiveProjection := True
  schurStarSquareProjection := True
  eulerArchimedeanCoherence := False
  adversarialTailBound := False
  noPostselectionSelector := False
  fakeFamilyFailure := False

/-- The Schur-only package satisfies the finite syntax rows. -/
theorem schurOnly_schurSyntaxRows : schurOnly.SchurSyntaxRows :=
  ⟨trivial, trivial, trivial⟩

/-- Schur/projection syntax alone does not supply Euler-loaded rows. -/
theorem schurSyntaxRows_do_not_supply_eulerLoadedRows :
    ∃ R : PrimitiveProjectionRows, R.SchurSyntaxRows ∧ ¬ R.EulerLoadedRows :=
  ⟨schurOnly, schurOnly_schurSyntaxRows, by
    intro h
    exact h.1⟩

/-- Schur/projection syntax alone does not supply the full projection gate. -/
theorem schurSyntaxRows_do_not_supply_holds :
    ∃ R : PrimitiveProjectionRows, R.SchurSyntaxRows ∧ ¬ R.Holds :=
  ⟨schurOnly, schurOnly_schurSyntaxRows, by
    intro h
    exact h.2.1⟩

end PrimitiveProjectionRows

/-!
## Schur-budget fake-blindness calibration
-/

namespace SchurBudgetCalibration

open SchurStarDominationCarrier

variable {Edge : Type*} [Fintype Edge]

/--
The Schur response-budget certificate survives every unit response twist.

This restates the existing absolute-budget fake-blindness theorem at the
primitive-projection gate: Schur algebra alone is not a named fake failure.
-/
theorem retwistedStar_nonnegative_of_responseBudget
    (A : SchurStarDominationCarrier.StarAssembly Edge)
    (twist : Edge -> ℝ)
    (x : ℝ) (y : Edge -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1)
    (harch : 0 < A.arch)
    (hbudget : A.responseBudget <= A.arch) :
    0 <=
      (AbsoluteBudgetFakeFamilyBlindness.StarAssembly.retwist A twist).form x y :=
  AbsoluteBudgetFakeFamilyBlindness.StarAssembly
    .form_nonnegative_retwist_of_responseBudget_le_arch
      A twist x y htwist harch hbudget

end SchurBudgetCalibration

/--
A primitive-projection source carrier.

`projectionRows` may discharge the explicit-source `noPostselectionFakeGate`
only through `noPostselectionFakeGate_of_projectionRows`, whose input is the
full Euler-loaded row package, not Schur syntax alone.
-/
structure ProjectionSourceCarrier where
  sourceCarrier :
    ChiralExplicitFormulaSource.ExplicitFormulaSourceCarrier.{u}
  projectionRows : PrimitiveProjectionRows
  noPostselectionFakeGate_of_projectionRows :
    projectionRows.Holds ->
      sourceCarrier.noPostselectionFakeGate

namespace ProjectionSourceCarrier

/--
Full projection-source rows: completed explicit-formula source rows,
same-carrier moment/trace identity, full Euler-loaded primitive projection,
and the remaining structural CPH rows.
-/
structure FaithfulRows (P : ProjectionSourceCarrier.{u}) : Prop where
  completedSourceRows : P.sourceCarrier.CompletedSourceRows
  sameCarrierRow : P.sourceCarrier.LiveSameCarrierRow
  projectionRows : P.projectionRows.Holds
  structuralRows : P.sourceCarrier.StructuralRows

/-- Faithful projection rows supply the explicit-formula source faithful rows. -/
theorem explicitSourceFaithfulRows_of_faithfulRows
    (P : ProjectionSourceCarrier.{u})
    (h : P.FaithfulRows) :
    P.sourceCarrier.FaithfulRows where
  completedSourceRows := h.completedSourceRows
  sameCarrierRow := h.sameCarrierRow
  noPostselectionFakeGate :=
    P.noPostselectionFakeGate_of_projectionRows h.projectionRows
  structuralRows := h.structuralRows

/-- Faithful projection rows supply the CPH packet rows. -/
theorem cphRows_of_faithfulRows
    (P : ProjectionSourceCarrier.{u})
    (h : P.FaithfulRows) :
    P.sourceCarrier.cphCarrier.CPHRows :=
  P.sourceCarrier.cphRows_of_faithfulRows
    (P.explicitSourceFaithfulRows_of_faithfulRows h)

/-- Faithful projection rows supply the Fredholm-squared endpoint rows. -/
theorem fredholmFaithfulRows_of_faithfulRows
    (P : ProjectionSourceCarrier.{u})
    (h : P.FaithfulRows) :
    P.sourceCarrier.cphCarrier.fredholmCarrier.FaithfulRows :=
  P.sourceCarrier.fredholmFaithfulRows_of_faithfulRows
    (P.explicitSourceFaithfulRows_of_faithfulRows h)

/-- Faithful projection rows prove mathlib's `RiemannHypothesis` conditionally. -/
theorem riemannHypothesis_of_faithfulRows
    (P : ProjectionSourceCarrier.{u})
    (h : P.FaithfulRows) :
    RiemannHypothesis :=
  P.sourceCarrier.riemannHypothesis_of_faithfulRows
    (P.explicitSourceFaithfulRows_of_faithfulRows h)

/-- A non-real regular `Xi` zero blocks faithful projection-source rows. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (P : ProjectionSourceCarrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ P.FaithfulRows := by
  intro h
  exact P.sourceCarrier.not_faithfulRows_of_nonrealRegularXiZero hz hzim
    (P.explicitSourceFaithfulRows_of_faithfulRows h)

end ProjectionSourceCarrier

/-!
## Diagnostic-only calibration
-/

/--
A projection source with Schur syntax rows but no Euler load and no fake gate.
-/
def schurOnlyProjectionSourceCarrier : ProjectionSourceCarrier.{0} where
  sourceCarrier := ChiralExplicitFormulaSource.diagnosticOnlySourceCarrier
  projectionRows := PrimitiveProjectionRows.schurOnly
  noPostselectionFakeGate_of_projectionRows := by
    intro h
    exact h.2.1

/--
Schur/projection syntax at the finite-algebra layer does not supply the
explicit-source no-postselection fake gate.
-/
theorem schurSyntaxRows_do_not_supply_noPostselectionFakeGate :
    ∃ P : ProjectionSourceCarrier.{0},
      P.projectionRows.SchurSyntaxRows ∧
        ¬ P.sourceCarrier.noPostselectionFakeGate :=
  ⟨schurOnlyProjectionSourceCarrier,
    PrimitiveProjectionRows.schurOnly_schurSyntaxRows,
    by
      intro h
      exact h⟩

/--
Schur/projection syntax alone does not supply faithful projection-source rows.
-/
theorem schurSyntaxRows_do_not_supply_faithfulRows :
    ∃ P : ProjectionSourceCarrier.{0},
      P.projectionRows.SchurSyntaxRows ∧ ¬ P.FaithfulRows :=
  ⟨schurOnlyProjectionSourceCarrier,
    PrimitiveProjectionRows.schurOnly_schurSyntaxRows,
    by
      intro h
      exact h.projectionRows.2.1⟩

/-- Existence of a faithful Euler-loaded primitive projection carrier. -/
def HasFaithfulEulerLoadedPrimitiveProjectionCarrier : Prop :=
  ∃ P : ProjectionSourceCarrier.{u}, P.FaithfulRows

/-- A faithful projection carrier supplies the explicit-formula source carrier. -/
theorem hasFaithfulExplicitFormulaSourceCarrier_of_hasFaithfulEulerLoadedPrimitiveProjectionCarrier
    (hP : HasFaithfulEulerLoadedPrimitiveProjectionCarrier.{u}) :
    ChiralExplicitFormulaSource.HasFaithfulExplicitFormulaSourceCarrier.{u} := by
  rcases hP with ⟨P, hrows⟩
  exact ⟨P.sourceCarrier, P.explicitSourceFaithfulRows_of_faithfulRows hrows⟩

/-- A faithful projection carrier proves mathlib's `RiemannHypothesis` conditionally. -/
theorem riemannHypothesis_of_hasFaithfulEulerLoadedPrimitiveProjectionCarrier
    (hP : HasFaithfulEulerLoadedPrimitiveProjectionCarrier.{u}) :
    RiemannHypothesis := by
  rcases hP with ⟨P, hrows⟩
  exact P.riemannHypothesis_of_faithfulRows hrows

/-- A non-real regular `Xi` zero rules out faithful projection carriers. -/
theorem not_hasFaithfulEulerLoadedPrimitiveProjectionCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulEulerLoadedPrimitiveProjectionCarrier.{u} := by
  rintro ⟨P, hrows⟩
  exact P.not_faithfulRows_of_nonrealRegularXiZero hz hzim hrows

/-- Packaged conditional RH certificate for the projection route. -/
structure EulerLoadedPrimitiveProjectionRHCertificate where
  carrier : ProjectionSourceCarrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace EulerLoadedPrimitiveProjectionRHCertificate

/-- The packaged projection certificate supplies explicit-source faithful rows. -/
theorem explicitSourceFaithfulRows
    (cert : EulerLoadedPrimitiveProjectionRHCertificate.{u}) :
    cert.carrier.sourceCarrier.FaithfulRows :=
  cert.carrier.explicitSourceFaithfulRows_of_faithfulRows cert.faithfulRows

/-- The packaged projection certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : EulerLoadedPrimitiveProjectionRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.carrier.riemannHypothesis_of_faithfulRows cert.faithfulRows

end EulerLoadedPrimitiveProjectionRHCertificate

end EulerLoadedPrimitiveProjection
end JensenLadder
