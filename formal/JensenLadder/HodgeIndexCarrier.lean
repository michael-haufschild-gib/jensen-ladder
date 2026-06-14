import JensenLadder.ArithmeticSiteCarrier

/-!
# Hodge-index carrier boundary

This file records the Lean-facing boundary for the sharpened F1/Hodge route.

The current obstruction is not the absence of a generic word like
"positivity"; it is the absence of a zeta-attached self-product carrier with an
intersection pairing, a Hodge-index signature theorem, a Frobenius
correspondence, and a Weil/Lefschetz trace identity that specializes to the
existing arithmetic-site handoff.

This module does not construct `Spec Z x_F1 Spec Z`, an intersection theory, a
Hodge-index theorem, a Frobenius correspondence, or RH.  It only names the rows
that such a construction must provide and proves their exact handoff to
`ArithmeticSiteCarrier`.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace HodgeIndexCarrier

open ArithmeticSiteCarrier

universe u

/--
An F1/Hodge-index-shaped carrier before it is collapsed into the existing
arithmetic-site interface.

The concrete mathematical object would be a self-product surface or equivalent
intersection carrier for compactified `Spec Z`.  The fields here are only the
boundary rows:

* `hodgeIndexSignature`: the intrinsic one-positive-direction / primitive
  negativity row for the intersection form;
* `frobeniusCorrespondence`: the arithmetic Frobenius or scaling-flow
  correspondence row;
* `weilTraceIdentity`: the specialization of that correspondence to the Weil
  explicit-formula trace row.

The adapter fields are where a real proof must supply non-circular mathematics:
the Hodge row must produce the arithmetic-site Hodge package, and the Frobenius
plus trace rows must produce the arithmetic-site Lefschetz trace formula.
-/
structure Carrier where
  SelfProduct : Type u
  DivisorClass : Type u
  intersectionForm : DivisorClass -> DivisorClass -> ℝ
  primitive : DivisorClass -> Prop
  ampleClass : DivisorClass
  hodgeIndexSignature : Prop
  frobeniusCorrespondence : Prop
  weilTraceIdentity : Prop
  arithmeticCarrier : ArithmeticSiteCarrier.Carrier.{u}
  hodgeIndexPackage_of_signature :
    hodgeIndexSignature -> arithmeticCarrier.hodgeIndexPackage
  lefschetzTraceFormula_of_frobenius_trace :
    frobeniusCorrespondence -> weilTraceIdentity ->
      arithmeticCarrier.lefschetzTraceFormula

/--
The Hodge-index rows required before the carrier can be handed to the existing
arithmetic-site endpoint.
-/
def Carrier.FaithfulRows (C : Carrier.{u}) : Prop :=
  C.arithmeticCarrier.frobeniusLifts ∧
    C.hodgeIndexSignature ∧
      C.frobeniusCorrespondence ∧ C.weilTraceIdentity

/-- The Hodge-index rows supply the arithmetic-site faithful rows. -/
theorem arithmeticFaithfulRows_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    C.arithmeticCarrier.FaithfulRows :=
  ⟨h.1,
    C.hodgeIndexPackage_of_signature h.2.1,
    C.lefschetzTraceFormula_of_frobenius_trace h.2.2.1 h.2.2.2⟩

/--
A non-circular Hodge-index carrier with all rows would prove mathlib's
`RiemannHypothesis`.
-/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  ArithmeticSiteCarrier.riemannHypothesis_of_faithfulRows C.arithmeticCarrier
    (arithmeticFaithfulRows_of_faithfulRows C h)

/-- A missing regular zero blocks the Weil trace identity row. -/
theorem not_weilTraceIdentity_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : DeningerCarrier.MissingRegularXiZero
      C.arithmeticCarrier.spectralCarrier)
    (hfrob : C.frobeniusCorrespondence) :
    ¬ C.weilTraceIdentity := by
  intro htrace
  exact ArithmeticSiteCarrier.not_lefschetzTraceFormula_of_missingRegularXiZero
    C.arithmeticCarrier hmiss
    (C.lefschetzTraceFormula_of_frobenius_trace hfrob htrace)

/-- A missing regular zero blocks the full Hodge-index handoff. -/
theorem not_faithfulRows_of_missingRegularXiZero
    (C : Carrier.{u})
    (hmiss : DeningerCarrier.MissingRegularXiZero
      C.arithmeticCarrier.spectralCarrier) :
    ¬ C.FaithfulRows := by
  intro hrows
  exact not_weilTraceIdentity_of_missingRegularXiZero C hmiss hrows.2.2.1
    hrows.2.2.2

/-- A non-real regular `Xi` zero blocks the Weil trace identity row. -/
theorem not_weilTraceIdentity_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0)
    (hfrob : C.frobeniusCorrespondence) :
    ¬ C.weilTraceIdentity :=
  not_weilTraceIdentity_of_missingRegularXiZero C
    (DeningerCarrier.missingRegularXiZero_of_nonrealRegularXiZero
      C.arithmeticCarrier.spectralCarrier hz hzim)
    hfrob

/-- A non-real regular `Xi` zero blocks the full Hodge-index handoff. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows :=
  not_faithfulRows_of_missingRegularXiZero C
    (DeningerCarrier.missingRegularXiZero_of_nonrealRegularXiZero
      C.arithmeticCarrier.spectralCarrier hz hzim)

/-- Existence of a faithful Hodge-index carrier. -/
def HasFaithfulHodgeIndexCarrier : Prop :=
  exists C : Carrier.{u}, C.FaithfulRows

/-- A faithful Hodge-index carrier supplies the arithmetic-site carrier. -/
theorem hasFaithfulArithmeticSiteCarrier_of_hasFaithfulHodgeIndexCarrier
    (hC : HasFaithfulHodgeIndexCarrier.{u}) :
    HasFaithfulArithmeticSiteCarrier.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨C.arithmeticCarrier, arithmeticFaithfulRows_of_faithfulRows C hrows⟩

/--
Circular calibration: any already faithful arithmetic-site carrier can be
relabeled as a Hodge-index carrier.

This deliberately uses `Option A.Site` for the self-product and divisor class,
and reuses the existing arithmetic rows.  It is a calibration, not a
construction of the missing F1 self-product or Hodge-index theorem.
-/
def hodgeIndexCarrierOfArithmeticSiteCarrier
    (A : ArithmeticSiteCarrier.Carrier.{u}) :
    Carrier.{u} where
  SelfProduct := Option A.Site
  DivisorClass := Option A.Site
  intersectionForm := fun _ _ => 0
  primitive := fun _ => True
  ampleClass := none
  hodgeIndexSignature := A.hodgeIndexPackage
  frobeniusCorrespondence := A.lefschetzTraceFormula
  weilTraceIdentity := True
  arithmeticCarrier := A
  hodgeIndexPackage_of_signature := by
    intro hsignature
    exact hsignature
  lefschetzTraceFormula_of_frobenius_trace := by
    intro htrace _hweil
    exact htrace

/-- The calibrated Hodge-index wrapper is faithful when the arithmetic carrier is. -/
theorem faithfulRows_hodgeIndexCarrierOfArithmeticFaithfulRows
    (A : ArithmeticSiteCarrier.Carrier.{u})
    (h : A.FaithfulRows) :
    (hodgeIndexCarrierOfArithmeticSiteCarrier A).FaithfulRows :=
  ⟨h.1, h.2.1, h.2.2, trivial⟩

/-- A faithful arithmetic-site carrier supplies the calibrated Hodge-index carrier. -/
theorem hasFaithfulHodgeIndexCarrier_of_hasFaithfulArithmeticSiteCarrier
    (hA : HasFaithfulArithmeticSiteCarrier.{u}) :
    HasFaithfulHodgeIndexCarrier.{u} := by
  rcases hA with ⟨A, hrows⟩
  exact ⟨hodgeIndexCarrierOfArithmeticSiteCarrier A,
    faithfulRows_hodgeIndexCarrierOfArithmeticFaithfulRows A hrows⟩

/--
The Hodge-index handoff has exactly the same strength as the arithmetic-site
handoff.

The reverse direction is the circular calibration above; it does not construct
the missing self-product surface, intersection form, or Frobenius
correspondence.
-/
theorem hasFaithfulHodgeIndexCarrier_iff_hasFaithfulArithmeticSiteCarrier :
    HasFaithfulHodgeIndexCarrier.{u} ↔
      HasFaithfulArithmeticSiteCarrier.{u} := by
  constructor
  · exact hasFaithfulArithmeticSiteCarrier_of_hasFaithfulHodgeIndexCarrier
  · exact hasFaithfulHodgeIndexCarrier_of_hasFaithfulArithmeticSiteCarrier

/--
At universe zero, the Hodge-index handoff has exactly RH strength.

The useful direction is the conditional F1/Hodge proof route.  The reverse
direction is only the tautological arithmetic-site calibration.
-/
theorem hasFaithfulHodgeIndexCarrier_iff_riemannHypothesis :
    HasFaithfulHodgeIndexCarrier.{0} ↔ RiemannHypothesis := by
  exact hasFaithfulHodgeIndexCarrier_iff_hasFaithfulArithmeticSiteCarrier.trans
    ArithmeticSiteCarrier.hasFaithfulArithmeticSiteCarrier_iff_riemannHypothesis

/-- A non-real regular `Xi` zero rules out every faithful Hodge-index carrier. -/
theorem not_hasFaithfulHodgeIndexCarrier_of_nonrealRegularXiZero
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ HasFaithfulHodgeIndexCarrier.{u} := by
  intro hC
  exact ArithmeticSiteCarrier.not_hasFaithfulArithmeticSiteCarrier_of_nonrealRegularXiZero
    hz hzim
    (hasFaithfulArithmeticSiteCarrier_of_hasFaithfulHodgeIndexCarrier hC)

/-- Packaged conditional certificate for the Hodge-index route. -/
structure HodgeIndexRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace HodgeIndexRHCertificate

/-- The packaged Hodge-index certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : HodgeIndexRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_faithfulRows C.carrier C.faithfulRows

/-- The packaged Hodge-index certificate supplies the arithmetic-site handoff. -/
theorem hasFaithfulArithmeticSiteCarrier
    (C : HodgeIndexRHCertificate.{u}) :
    HasFaithfulArithmeticSiteCarrier.{u} :=
  ⟨C.carrier.arithmeticCarrier,
    arithmeticFaithfulRows_of_faithfulRows C.carrier C.faithfulRows⟩

end HodgeIndexRHCertificate

end HodgeIndexCarrier
end JensenLadder
