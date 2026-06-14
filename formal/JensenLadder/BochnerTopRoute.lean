import JensenLadder.MorseCriterion
import Mathlib.Tactic

/-!
# Bochner simple-top route control

This module translates a Bochner-style "simple top eigenvalue" formulation into
the existing Morse bottom-eigenvalue interface.

The sign convention is supplied explicitly by `bottom_eq_neg_top`: the Morse
bottom value is the negative of the Bochner top value.  Under that convention,
the RH-bearing row is `top ≤ 0` at every scale, equivalently nonnegativity of
the calibrated Morse bottom.  The simple-top row is useful route-control
metadata, but it carries no sign information by itself.

This file does not construct a Bochner operator, prove a Bochner identity, prove
self-adjointness, prove simplicity for a concrete zeta family, prove a
finite-to-limit convergence theorem, or prove RH.  Evidence class:
formal/certificate artifact and dead-end elimination.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace BochnerTopRoute

open MorseCriterion

universe u

/--
Signed top-eigenvalue data for a supplied Morse/RH criterion.

`top` is the Bochner-side value, `bottomCalibration.bottom` is the Morse-side
value, and `bottom_eq_neg_top` is the sign convention connecting them.  The
`simpleTop` predicate is deliberately separate from the sign row.
-/
structure SignedTopCalibration (C : MorseIndexRHEquivalence.{u}) where
  bottomCalibration : LowestEigenvalueCalibration C
  top : C.Scale -> ℝ
  bottom_eq_neg_top :
    ∀ a : C.Scale, bottomCalibration.bottom a = - top a
  simpleTop : C.Scale -> Prop

namespace SignedTopCalibration

/-- The Bochner-side sign row corresponding to nonnegative Morse bottom. -/
def NonpositiveTop {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) : Prop :=
  ∀ a : C.Scale, B.top a ≤ 0

/-- The simple-top route-control row at every scale. -/
def SimpleTops {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) : Prop :=
  ∀ a : C.Scale, B.simpleTop a

/-- The simple-top route-control row at one scale. -/
def SimpleTopAt {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) (a : C.Scale) : Prop :=
  B.simpleTop a

/-- A signed top calibration induces the existing simple-bottom metadata. -/
def toSimpleBottomCalibration {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) :
    SimpleBottomCalibration B.bottomCalibration where
  simpleBottom := B.simpleTop

/-- Simple top at every scale is definitionally the same metadata as simple
bottom for the induced bottom calibration. -/
theorem simpleBottoms_iff_simpleTops {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) :
    SimpleBottomCalibration.SimpleBottoms (B.toSimpleBottomCalibration) ↔
      B.SimpleTops := by
  rfl

/-- The signed top row is exactly the nonnegative-bottom row. -/
theorem nonnegativeBottom_iff_nonpositiveTop {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) :
    NonnegativeBottom B.bottomCalibration.bottom ↔ B.NonpositiveTop := by
  constructor
  · intro hbottom a
    have hb : 0 ≤ B.bottomCalibration.bottom a := hbottom a
    rw [B.bottom_eq_neg_top a] at hb
    linarith
  · intro htop a
    have ht : B.top a ≤ 0 := htop a
    rw [B.bottom_eq_neg_top a]
    linarith

/--
Under a supplied Morse/RH criterion and signed top calibration, RH is equivalent
to the Bochner-side nonpositive-top row.
-/
theorem riemannHypothesis_iff_nonpositiveTop {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) :
    RiemannHypothesis ↔ B.NonpositiveTop :=
  (LowestEigenvalueCalibration.riemannHypothesis_iff_nonnegativeBottom
    C B.bottomCalibration).trans (B.nonnegativeBottom_iff_nonpositiveTop)

/--
Simple tops plus the actual sign row prove RH.  The proof ignores simplicity
except as route-control metadata; the sign row is load-bearing.
-/
theorem riemannHypothesis_of_simpleTops_and_nonpositiveTop
    {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C)
    (_hsimple : B.SimpleTops)
    (htop : B.NonpositiveTop) :
    RiemannHypothesis :=
  (B.riemannHypothesis_iff_nonpositiveTop).2 htop

/--
A simple top with the wrong sign at one scale is a falsifier under the supplied
Morse/RH criterion.
-/
theorem not_riemannHypothesis_of_simpleTopAt_and_top_pos
    {C : MorseIndexRHEquivalence.{u}}
    (B : SignedTopCalibration C) {a : C.Scale}
    (_hsimple : B.SimpleTopAt a)
    (ha : 0 < B.top a) :
    ¬ RiemannHypothesis := by
  have hbottom : B.bottomCalibration.bottom a < 0 := by
    rw [B.bottom_eq_neg_top a]
    linarith
  exact LowestEigenvalueCalibration.not_riemannHypothesis_of_bottom_lt
    B.bottomCalibration hbottom

/-- Packaged RH certificate for the signed Bochner-top route. -/
structure SignedTopRHCertificate (C : MorseIndexRHEquivalence.{u}) where
  calibration : SignedTopCalibration C
  simpleTops : calibration.SimpleTops
  top_nonpositive : calibration.NonpositiveTop

namespace SignedTopRHCertificate

/-- A packaged signed-top certificate proves RH because it includes the sign row. -/
theorem riemannHypothesis
    {C : MorseIndexRHEquivalence.{u}}
    (cert : SignedTopRHCertificate C) :
    RiemannHypothesis :=
  cert.calibration.riemannHypothesis_of_simpleTops_and_nonpositiveTop
    cert.simpleTops cert.top_nonpositive

/-- Forgetting to the existing simple-bottom certificate makes the sign row
explicit as bottom nonnegativity. -/
def toSimpleBottomRHCertificate
    {C : MorseIndexRHEquivalence.{u}}
    (cert : SignedTopRHCertificate C) :
    SimpleBottomCalibration.SimpleBottomRHCertificate C where
  calibration := cert.calibration.bottomCalibration
  simplicity := cert.calibration.toSimpleBottomCalibration
  simpleBottoms :=
    (cert.calibration.simpleBottoms_iff_simpleTops).2 cert.simpleTops
  bottom_nonnegative :=
    (cert.calibration.nonnegativeBottom_iff_nonpositiveTop).2
      cert.top_nonpositive

end SignedTopRHCertificate

/-- Packaged falsifier for a signed top calibration at one scale. -/
structure SignedTopFalsifier (C : MorseIndexRHEquivalence.{u}) where
  calibration : SignedTopCalibration C
  scale : C.Scale
  simpleTopAt : calibration.SimpleTopAt scale
  top_pos : 0 < calibration.top scale

namespace SignedTopFalsifier

/-- A packaged wrong-sign simple top refutes RH under the supplied criterion. -/
theorem not_riemannHypothesis
    {C : MorseIndexRHEquivalence.{u}}
    (cert : SignedTopFalsifier C) :
    ¬ RiemannHypothesis :=
  cert.calibration.not_riemannHypothesis_of_simpleTopAt_and_top_pos
    cert.simpleTopAt cert.top_pos

end SignedTopFalsifier

end SignedTopCalibration

end BochnerTopRoute
end JensenLadder
