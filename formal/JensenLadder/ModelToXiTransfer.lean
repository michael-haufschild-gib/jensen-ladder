import JensenLadder.XiJensen
import JensenLadder.RHReduction

/-!
# Model-to-Xi transfer boundary

This file isolates the exact formal shape of the remaining model-to-Xi bridge.
It does not prove the bridge.  It only states the proof interface:

* a model endpoint supplies hyperbolicity for the model section at every valid
  degree;
* a fake-zero-free transfer row carries each model section to the corresponding
  actual Xi Jensen section;
* the classical Jensen/Laguerre-Polya gate then turns all actual Xi Jensen
  sections into reality of all regular Xi zeros, hence `RiemannHypothesis`.

The load-bearing analytic input is the transfer row, not this wrapper.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ModelToXiTransfer

universe u

/--
Abstract data for one model family and its target Xi Jensen family.

`model_endpoint` is the formal slot where a theorem such as Theorem M may be
plugged in after matching conventions.  It only proves the model side.  The
actual Xi side is intentionally separate: that is the fake-zero-free transport
problem.
-/
structure ModelEndpointData where
  Degree : Type u
  validDegree : Degree -> Prop
  modelHyperbolic : Degree -> Prop
  xiHyperbolic : Degree -> Prop
  model_endpoint : forall d, validDegree d -> modelHyperbolic d

/--
The transfer row needed to cross from the model endpoint to the actual Xi
Jensen endpoint degree by degree.

This is the named place where a proposed Hurwitz, multiplier-sequence,
Lorentzian, or Bochner transfer has to exclude the fake-zero band.
-/
def FakeZeroFreeTransferRow (D : ModelEndpointData.{u}) : Prop :=
  forall d, D.validDegree d -> D.modelHyperbolic d -> D.xiHyperbolic d

/-- All actual Xi Jensen sections in the chosen degree range are hyperbolic. -/
def AllXiJensenHyperbolic (D : ModelEndpointData.{u}) : Prop :=
  forall d, D.validDegree d -> D.xiHyperbolic d

/--
The classical Jensen/Laguerre-Polya gate, specialized to this abstract family.

This is a general entire-function criterion: once all actual Xi Jensen sections
are hyperbolic, all regular zeros of `Xi` are real.  It is not supplied by
Theorem M, and it is not the model-to-Xi transfer row.
-/
def XiJensenClassicalGate (D : ModelEndpointData.{u}) : Prop :=
  AllXiJensenHyperbolic D ->
    (forall z : ℂ, RHReduction.riemannXiRegularZero z -> z.im = 0)

/--
A concrete valid degree whose actual Xi Jensen section is not hyperbolic.

Such a witness does not contradict model hyperbolicity.  It falsifies the
degreewise transfer row for the chosen model/target interface.
-/
def ValidXiSectionCounterexample (D : ModelEndpointData.{u}) : Prop :=
  exists d, D.validDegree d ∧ ¬ D.xiHyperbolic d

/--
Model endpoint hyperbolicity plus the fake-zero-free transfer row gives all
actual Xi Jensen sections.
-/
theorem allXiJensenHyperbolic_of_transfer
    (D : ModelEndpointData.{u})
    (hTransfer : FakeZeroFreeTransferRow D) :
    AllXiJensenHyperbolic D := by
  intro d hd
  exact hTransfer d hd (D.model_endpoint d hd)

/-- Degreewise version of `allXiJensenHyperbolic_of_transfer`. -/
theorem xiHyperbolic_of_transfer
    (D : ModelEndpointData.{u})
    (hTransfer : FakeZeroFreeTransferRow D)
    (d : D.Degree)
    (hd : D.validDegree d) :
    D.xiHyperbolic d :=
  allXiJensenHyperbolic_of_transfer D hTransfer d hd

/-- A bad actual Xi section rules out the all-sections Xi Jensen endpoint. -/
theorem not_allXiJensenHyperbolic_of_badXiSection
    (D : ModelEndpointData.{u})
    (hbad : ValidXiSectionCounterexample D) :
    ¬ AllXiJensenHyperbolic D := by
  intro hAll
  rcases hbad with ⟨d, hd, hnot⟩
  exact hnot (hAll d hd)

/--
A bad actual Xi section rules out the fake-zero-free transfer row, even if the
model endpoint itself is available at that degree.
-/
theorem not_transferRow_of_badXiSection
    (D : ModelEndpointData.{u})
    (hbad : ValidXiSectionCounterexample D) :
    ¬ FakeZeroFreeTransferRow D := by
  intro hTransfer
  exact not_allXiJensenHyperbolic_of_badXiSection D hbad
    (allXiJensenHyperbolic_of_transfer D hTransfer)

/--
The precise conditional theorem:

`model endpoint + fake-zero-free transfer row + classical Jensen gate -> RH`.

This theorem is only a composition of named assumptions with the already
kernel-checked `RHReduction` bridge.
-/
theorem riemannHypothesis_of_transfer_and_classicalGate
    (D : ModelEndpointData.{u})
    (hTransfer : FakeZeroFreeTransferRow D)
    (hClassicalGate : XiJensenClassicalGate D) :
    RiemannHypothesis :=
  RHReduction.riemannHypothesis_of_classicalGate_and_hyperbolicity
    (XiHyperbolic := AllXiJensenHyperbolic D)
    hClassicalGate
    (allXiJensenHyperbolic_of_transfer D hTransfer)

/-- Packaged certificate form for the model-to-Xi route. -/
structure ModelToXiRHCertificate where
  data : ModelEndpointData.{u}
  transferRow : FakeZeroFreeTransferRow data
  classicalGate : XiJensenClassicalGate data

/-- A packaged model-to-Xi certificate implies mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_certificate
    (C : ModelToXiRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_transfer_and_classicalGate C.data C.transferRow C.classicalGate

end ModelToXiTransfer
end JensenLadder
