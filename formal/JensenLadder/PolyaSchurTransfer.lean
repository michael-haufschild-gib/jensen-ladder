import JensenLadder.ModelToXiTransfer

/-!
# Polya-Schur transfer boundary

This file records the clean carrier-free form of the Lane B transfer attempt:

* a proven model entire function belongs to the Laguerre-Polya class;
* the coefficient ratio from the model to the actual Xi function is a
  Polya-Schur multiplier sequence;
* the standard Polya-Schur/Jensen machinery then carries the model endpoint to
  the actual Xi Jensen endpoint.

The file does not formalize Laguerre-Polya theory itself.  Those classical rows
remain explicit fields in `PolyaSchurTransferData`.  The point is to name the
load-bearing multiplier-sequence hypothesis and show exactly how it composes
with the existing `ModelToXiTransfer` and `RHReduction` interfaces.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace PolyaSchurTransfer

open ModelToXiTransfer

universe u

/--
Abstract data for the Polya-Schur route from a proven model endpoint to the
actual Xi endpoint.

`model_lp_endpoint` is where a theorem such as Theorem M may enter after the
model family has been matched to a Laguerre-Polya entire function.  The
load-bearing open hypothesis is `multiplierSequence`: the coefficient ratio
from the model to Xi must be a multiplier sequence.  The two classical rows are
kept explicit:

* `polyaSchurTransfer`: model LP plus multiplier sequence gives Xi LP;
* `xiSections_of_laguerrePolya`: Xi LP gives all Xi Jensen sections.
-/
structure PolyaSchurTransferData (T : ModelEndpointData.{u}) where
  modelInLaguerrePolya : Prop
  xiInLaguerrePolya : Prop
  multiplierSequence : Prop
  model_lp_endpoint : modelInLaguerrePolya
  polyaSchurTransfer : modelInLaguerrePolya -> multiplierSequence -> xiInLaguerrePolya
  xiSections_of_laguerrePolya : xiInLaguerrePolya -> AllXiJensenHyperbolic T

/-- A failed Xi Laguerre-Polya endpoint blocks the multiplier-sequence route. -/
def XiLaguerrePolyaCounterexample {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T) : Prop :=
  ¬ P.xiInLaguerrePolya

/-- A failed all-Jensen endpoint blocks the multiplier-sequence route. -/
def XiJensenCounterexample (T : ModelEndpointData.{u}) : Prop :=
  ¬ AllXiJensenHyperbolic T

/-- Model LP plus the multiplier-sequence hypothesis gives the Xi LP endpoint. -/
theorem xiInLaguerrePolya_of_multiplierSequence
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hMultiplier : P.multiplierSequence) :
    P.xiInLaguerrePolya :=
  P.polyaSchurTransfer P.model_lp_endpoint hMultiplier

/--
The Polya-Schur route supplies the all-Xi-Jensen endpoint once the multiplier
sequence hypothesis is available.
-/
theorem allXiJensenHyperbolic_of_multiplierSequence
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hMultiplier : P.multiplierSequence) :
    AllXiJensenHyperbolic T :=
  P.xiSections_of_laguerrePolya
    (xiInLaguerrePolya_of_multiplierSequence P hMultiplier)

/--
A multiplier sequence gives the degreewise fake-zero-free transfer row required
by `ModelToXiTransfer`.

This is stronger than the bare degreewise transfer: it proves all actual Xi
Jensen sections first and then forgets the degreewise model hypothesis.
-/
theorem fakeZeroFreeTransferRow_of_multiplierSequence
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hMultiplier : P.multiplierSequence) :
    FakeZeroFreeTransferRow T := by
  intro d hd _hmodel
  exact allXiJensenHyperbolic_of_multiplierSequence P hMultiplier d hd

/--
Conditional RH theorem for the multiplier route:

`model LP endpoint + multiplier sequence + classical Jensen gate -> RH`.

The multiplier sequence is the named open burden.  This theorem is only the
formal composition of that burden with already-separated classical rows.
-/
theorem riemannHypothesis_of_multiplierSequence_and_classicalGate
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hMultiplier : P.multiplierSequence)
    (hClassicalGate : XiJensenClassicalGate T) :
    RiemannHypothesis :=
  riemannHypothesis_of_transfer_and_classicalGate T
    (fakeZeroFreeTransferRow_of_multiplierSequence P hMultiplier)
    hClassicalGate

/-- If Xi is not in the Laguerre-Polya endpoint, the ratio is not a multiplier sequence. -/
theorem not_multiplierSequence_of_xi_not_laguerrePolya
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hbad : XiLaguerrePolyaCounterexample P) :
    ¬ P.multiplierSequence := by
  intro hMultiplier
  exact hbad (xiInLaguerrePolya_of_multiplierSequence P hMultiplier)

/-- If all actual Xi Jensen sections fail, the ratio is not a multiplier sequence. -/
theorem not_multiplierSequence_of_xi_jensen_counterexample
    {T : ModelEndpointData.{u}}
    (P : PolyaSchurTransferData T)
    (hbad : XiJensenCounterexample T) :
    ¬ P.multiplierSequence := by
  intro hMultiplier
  exact hbad (allXiJensenHyperbolic_of_multiplierSequence P hMultiplier)

/-- Packaged certificate form for the Polya-Schur route. -/
structure PolyaSchurRHCertificate (T : ModelEndpointData.{u}) where
  transferData : PolyaSchurTransferData T
  multiplierSequence : transferData.multiplierSequence
  classicalGate : XiJensenClassicalGate T

/-- A packaged Polya-Schur transfer certificate implies mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_certificate
    {T : ModelEndpointData.{u}}
    (C : PolyaSchurRHCertificate T) :
    RiemannHypothesis :=
  riemannHypothesis_of_multiplierSequence_and_classicalGate
    C.transferData C.multiplierSequence C.classicalGate

end PolyaSchurTransfer
end JensenLadder
