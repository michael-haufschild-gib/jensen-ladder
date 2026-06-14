import JensenLadder.HodgeIndexCarrier

/-!
# Geometric square-root carrier boundary

This file records the Lean-facing boundary for the SUSY / Dirac-square route.

An abstract square root of a Weil form is not a proof engine: existence of a
square-root presentation is equivalent to nonnegativity of the form once the
codomain norm-square is allowed to be arbitrary.  The non-circular content would
be a *geometric* square root: a Dirac-type operator built independently of RH,
whose square is the Weil form and whose trace identity hands off to the
F1/Hodge-index carrier.

This module therefore does two things:

* formalizes the circularity warning for an abstract square root;
* names the geometric square-root rows that must feed the existing
  `HodgeIndexCarrier` endpoint.

It does not construct a Connes--Consani spectral triple, prove `D^2 = Q_W`,
prove a Hodge-index theorem, prove a trace formula, or prove RH.  It only
separates the square-root handoff from the already-formalized Hodge carrier.

Evidence class: formal/certificate artifact + dead-end elimination.  Theorem M
is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace GeometricSquareRootCarrier

universe u

/-- Pointwise nonnegativity of a real-valued quadratic/Weil form. -/
def NonnegativeForm {State : Type u} (q : State -> ℝ) : Prop :=
  ∀ x : State, 0 ≤ q x

/--
An abstract square-root presentation of a real-valued form.

This is deliberately abstract: `RootState` and `normSq` are arbitrary.  The
theorem `nonempty_abstractSquareRoot_iff_nonnegativeForm` below is the formal
warning that such a presentation has exactly positivity strength unless the
root object is supplied by independent geometry.
-/
structure AbstractSquareRoot {State : Type u} (q : State -> ℝ) where
  RootState : Type u
  root : State -> RootState
  normSq : RootState -> ℝ
  normSq_nonnegative : ∀ y : RootState, 0 ≤ normSq y
  squareIdentity : ∀ x : State, q x = normSq (root x)

/-- An abstract square-root presentation makes the form nonnegative. -/
theorem nonnegativeForm_of_abstractSquareRoot
    {State : Type u} {q : State -> ℝ}
    (S : AbstractSquareRoot q) :
    NonnegativeForm q := by
  intro x
  rw [S.squareIdentity x]
  exact S.normSq_nonnegative (S.root x)

/--
Any already nonnegative form has a tautological abstract square-root
presentation.

This is the circular direction: it builds the "root" from the original state
space and uses the form itself as the norm-square.
-/
def abstractSquareRootOfNonnegativeForm
    {State : Type u} {q : State -> ℝ}
    (h : NonnegativeForm q) :
    AbstractSquareRoot q where
  RootState := State
  root := id
  normSq := q
  normSq_nonnegative := h
  squareIdentity := by
    intro _
    rfl

/--
Abstract square-root existence is exactly pointwise nonnegativity.

Thus "`Q_W` is a square" is not a non-circular route by itself.  The missing
row is a geometric construction of the square root, not this tautological
interface.
-/
theorem nonempty_abstractSquareRoot_iff_nonnegativeForm
    {State : Type u} (q : State -> ℝ) :
    Nonempty (AbstractSquareRoot q) ↔ NonnegativeForm q := by
  constructor
  · rintro ⟨S⟩
    exact nonnegativeForm_of_abstractSquareRoot S
  · intro h
    exact ⟨abstractSquareRootOfNonnegativeForm h⟩

/--
A geometric square-root carrier before it is collapsed into the existing
Hodge-index endpoint.

The `diracSquareIdentity` fields record the formal "D squared is the Weil
form" shape.  The proposition `geometricSquareRoot` is the genuinely external
row: it says the square root is constructed by independent geometry rather than
by the tautological nonnegative-form wrapper above.  The adapter fields are
where such a construction must supply the Hodge signature and trace rows.
-/
structure Carrier where
  Geometry : Type u
  TestFunction : Type u
  DiracState : Type u
  weilForm : TestFunction -> ℝ
  dirac : TestFunction -> DiracState
  diracNormSq : DiracState -> ℝ
  diracNormSq_nonnegative : ∀ y : DiracState, 0 ≤ diracNormSq y
  diracSquareIdentity : ∀ f : TestFunction, weilForm f = diracNormSq (dirac f)
  geometricSquareRoot : Prop
  traceCompatibility : Prop
  hodgeCarrier : HodgeIndexCarrier.Carrier.{u}
  hodgeIndexSignature_of_geometricSquareRoot :
    geometricSquareRoot -> hodgeCarrier.hodgeIndexSignature
  weilTraceIdentity_of_traceCompatibility :
    traceCompatibility -> hodgeCarrier.weilTraceIdentity

/-- The Dirac square fields give an abstract square-root presentation. -/
def Carrier.abstractSquareRoot (C : Carrier.{u}) :
    AbstractSquareRoot C.weilForm where
  RootState := C.DiracState
  root := C.dirac
  normSq := C.diracNormSq
  normSq_nonnegative := C.diracNormSq_nonnegative
  squareIdentity := C.diracSquareIdentity

/-- The Dirac square identity makes the Weil form nonnegative. -/
theorem Carrier.weilForm_nonnegative
    (C : Carrier.{u}) :
    NonnegativeForm C.weilForm :=
  nonnegativeForm_of_abstractSquareRoot C.abstractSquareRoot

/--
The square-root rows required before the carrier can be handed to the existing
Hodge-index endpoint.
-/
def Carrier.FaithfulRows (C : Carrier.{u}) : Prop :=
  C.hodgeCarrier.arithmeticCarrier.frobeniusLifts ∧
    C.geometricSquareRoot ∧
      C.hodgeCarrier.frobeniusCorrespondence ∧ C.traceCompatibility

/-- The geometric square-root rows supply the Hodge-index faithful rows. -/
theorem hodgeFaithfulRows_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.hodgeCarrier.FaithfulRows :=
  ⟨h.1,
    C.hodgeIndexSignature_of_geometricSquareRoot h.2.1,
    h.2.2.1,
    C.weilTraceIdentity_of_traceCompatibility h.2.2.2⟩

/--
A non-circular geometric square-root carrier with all handoff rows would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  HodgeIndexCarrier.riemannHypothesis_of_faithfulRows C.hodgeCarrier
    (hodgeFaithfulRows_of_faithfulRows C h)

/-- Existence of a faithful geometric square-root carrier. -/
def HasFaithfulGeometricSquareRootCarrier : Prop :=
  exists C : Carrier.{u}, C.FaithfulRows

/-- A faithful geometric square-root carrier supplies the Hodge-index carrier. -/
theorem hasFaithfulHodgeIndexCarrier_of_hasFaithfulGeometricSquareRootCarrier
    (hC : HasFaithfulGeometricSquareRootCarrier.{u}) :
    HodgeIndexCarrier.HasFaithfulHodgeIndexCarrier.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.hodgeCarrier, hodgeFaithfulRows_of_faithfulRows C hrows⟩

/--
Circular calibration: any already faithful Hodge-index carrier can be relabeled
as a geometric square-root carrier.

This uses the zero form and reuses the existing Hodge rows.  It is a
calibration, not a construction of a geometric Dirac operator or the identity
`D^2 = Q_W` for the zeta Weil form.
-/
def geometricSquareRootCarrierOfHodgeIndexCarrier
    (H : HodgeIndexCarrier.Carrier.{u}) :
    Carrier.{u} where
  Geometry := H.SelfProduct
  TestFunction := Option H.SelfProduct
  DiracState := Option H.SelfProduct
  weilForm := fun _ => 0
  dirac := fun x => x
  diracNormSq := fun _ => 0
  diracNormSq_nonnegative := by
    intro _
    exact le_rfl
  diracSquareIdentity := by
    intro _
    rfl
  geometricSquareRoot := H.hodgeIndexSignature
  traceCompatibility := H.weilTraceIdentity
  hodgeCarrier := H
  hodgeIndexSignature_of_geometricSquareRoot := by
    intro hsignature
    exact hsignature
  weilTraceIdentity_of_traceCompatibility := by
    intro htrace
    exact htrace

/-- The calibrated square-root wrapper is faithful when the Hodge carrier is. -/
theorem faithfulRows_geometricSquareRootCarrierOfHodgeFaithfulRows
    (H : HodgeIndexCarrier.Carrier.{u})
    (h : H.FaithfulRows) :
    (geometricSquareRootCarrierOfHodgeIndexCarrier H).FaithfulRows :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A faithful Hodge-index carrier supplies the calibrated square-root carrier. -/
theorem hasFaithfulGeometricSquareRootCarrier_of_hasFaithfulHodgeIndexCarrier
    (hH : HodgeIndexCarrier.HasFaithfulHodgeIndexCarrier.{u}) :
    HasFaithfulGeometricSquareRootCarrier.{u} := by
  rcases hH with ⟨H, hrows⟩
  exact ⟨geometricSquareRootCarrierOfHodgeIndexCarrier H,
    faithfulRows_geometricSquareRootCarrierOfHodgeFaithfulRows H hrows⟩

/--
The geometric square-root handoff has exactly the same strength as the
Hodge-index handoff.

The reverse direction is the circular calibration above; it does not construct
the missing geometric Dirac operator.
-/
theorem hasFaithfulGeometricSquareRootCarrier_iff_hasFaithfulHodgeIndexCarrier :
    HasFaithfulGeometricSquareRootCarrier.{u} ↔
      HodgeIndexCarrier.HasFaithfulHodgeIndexCarrier.{u} := by
  constructor
  · exact hasFaithfulHodgeIndexCarrier_of_hasFaithfulGeometricSquareRootCarrier
  · exact hasFaithfulGeometricSquareRootCarrier_of_hasFaithfulHodgeIndexCarrier

/--
At universe zero, the geometric square-root handoff has exactly RH strength.

The useful direction is the conditional square-root proof route.  The reverse
direction is only the tautological Hodge-index calibration.
-/
theorem hasFaithfulGeometricSquareRootCarrier_iff_riemannHypothesis :
    HasFaithfulGeometricSquareRootCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulGeometricSquareRootCarrier_iff_hasFaithfulHodgeIndexCarrier.trans
    HodgeIndexCarrier.hasFaithfulHodgeIndexCarrier_iff_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful square-root carrier. -/
theorem not_hasFaithfulGeometricSquareRootCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulGeometricSquareRootCarrier.{u} := by
  intro hC
  exact HodgeIndexCarrier.not_hasFaithfulHodgeIndexCarrier_of_nonrealRegularXiZero
    hz hzim
    (hasFaithfulHodgeIndexCarrier_of_hasFaithfulGeometricSquareRootCarrier hC)

/-- Packaged conditional certificate for the geometric square-root route. -/
structure GeometricSquareRootRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace GeometricSquareRootRHCertificate

/-- The packaged square-root certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : GeometricSquareRootRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_faithfulRows C.carrier C.faithfulRows

/-- The packaged square-root certificate supplies the Hodge-index handoff. -/
theorem hasFaithfulHodgeIndexCarrier
    (C : GeometricSquareRootRHCertificate.{u}) :
    HodgeIndexCarrier.HasFaithfulHodgeIndexCarrier.{u} :=
  ⟨C.carrier.hodgeCarrier,
    hodgeFaithfulRows_of_faithfulRows C.carrier C.faithfulRows⟩

/-- The packaged square-root certificate makes its Weil form nonnegative. -/
theorem weilForm_nonnegative
    (C : GeometricSquareRootRHCertificate.{u}) :
    NonnegativeForm C.carrier.weilForm :=
  Carrier.weilForm_nonnegative C.carrier

end GeometricSquareRootRHCertificate

end GeometricSquareRootCarrier
end JensenLadder
