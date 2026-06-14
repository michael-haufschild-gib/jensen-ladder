import JensenLadder.SquaredVariablePullback

/-!
# Ordinary Fredholm squared carrier boundary

This module records the Lean-facing form of the anomaly-free squared carrier
target:

```text
  det(I - w A) = Phi(sqrt w) / Phi(0)
```

with `A = T T*` positive trace-class and `T` Hilbert--Schmidt.  In the
abstract interface below, `energy` is the nonnegative squared spectrum of the
positive trace-class operator.  The load-bearing row is not positivity by
itself, nor trace-class bookkeeping by itself, but the Fredholm-determinant
identity strong enough to represent every regular `Xi` zero by a point of that
nonnegative squared spectrum.

The file deliberately treats trace-class, Hilbert--Schmidt, and determinant
identity rows as propositions.  It does not construct a Fredholm determinant,
prove trace-ideal facts, build `T`, prove the Hadamard order-`1/2` product, or
prove RH.  It only pins the exact handoff into the already formalized
`SquaredVariablePullback` consumer.

Evidence class: formal/certificate artifact; carrier boundary.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace FredholmSquaredCarrier

open SquaredVariablePullback

universe u

/--
Abstract data for an ordinary squared Fredholm carrier.

`positiveSquare` is the positivity of `A = T T*`.
`traceClassSquare` and `hilbertSchmidtRoot` record the trace-ideal class
expected from the order-`1/2` squared target.  `fredholmDeterminantIdentity` is
the actual spectral-identification row: together with the trace-ideal rows, it
must imply that every regular `Xi` zero has `z^2` in the nonnegative squared
spectrum.
-/
structure Carrier where
  Spectrum : Type u
  energy : Spectrum -> ℝ
  positiveSquare : Prop
  traceClassSquare : Prop
  hilbertSchmidtRoot : Prop
  fredholmDeterminantIdentity : Prop
  nonnegative_of_positiveSquare :
    positiveSquare -> NonnegativeSquaredSupport energy
  complete_of_fredholmRows :
    traceClassSquare ->
      hilbertSchmidtRoot ->
        fredholmDeterminantIdentity ->
          ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
            ∃ γ : Spectrum, z ^ 2 = (energy γ : ℂ)

namespace Carrier

/--
The rows required before the ordinary Fredholm carrier can be consumed by the
squared-variable RH endpoint.
-/
def FaithfulRows (C : Carrier.{u}) : Prop :=
  C.positiveSquare ∧
    C.traceClassSquare ∧ C.hilbertSchmidtRoot ∧ C.fredholmDeterminantIdentity

/-- Faithful Fredholm rows supply exact nonnegative squared support. -/
theorem regularXiNonnegativeSquaredSupport_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RegularXiNonnegativeSquaredSupport C.energy := by
  refine ⟨C.nonnegative_of_positiveSquare h.1, ?_⟩
  intro z hz
  exact C.complete_of_fredholmRows h.2.1 h.2.2.1 h.2.2.2 z hz

/--
A non-circular ordinary Fredholm squared carrier with faithful rows would prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_faithfulRows
    (C : Carrier.{u})
    (h : C.FaithfulRows) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeSquaredSupport
    (regularXiNonnegativeSquaredSupport_of_faithfulRows C h)

/-- A regular `Xi` zero not represented in the squared spectrum. -/
def MissingRegularSquaredZero (C : Carrier.{u}) : Prop :=
  ∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧
    ∀ γ : C.Spectrum, z ^ 2 ≠ (C.energy γ : ℂ)

/-- A missing squared zero falsifies the Fredholm determinant identity once the
trace-ideal rows are fixed. -/
theorem not_fredholmDeterminantIdentity_of_missingRegularSquaredZero
    (C : Carrier.{u})
    (htrace : C.traceClassSquare)
    (hroot : C.hilbertSchmidtRoot)
    (hmiss : C.MissingRegularSquaredZero) :
    ¬ C.fredholmDeterminantIdentity := by
  intro hdet
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases C.complete_of_fredholmRows htrace hroot hdet z hz with ⟨γ, hγ⟩
  exact hmissing γ hγ

/-- A missing squared zero blocks faithful Fredholm rows. -/
theorem not_faithfulRows_of_missingRegularSquaredZero
    (C : Carrier.{u})
    (hmiss : C.MissingRegularSquaredZero) :
    ¬ C.FaithfulRows := by
  intro h
  exact C.not_fredholmDeterminantIdentity_of_missingRegularSquaredZero
    h.2.1 h.2.2.1 hmiss h.2.2.2

/-- A nonreal regular `Xi` zero is a squared-spectrum obstruction for every
faithful positive Fredholm carrier. -/
theorem not_faithfulRows_of_nonrealRegularXiZero
    (C : Carrier.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ C.FaithfulRows := by
  intro h
  have hsupport :
      RegularXiNonnegativeSquaredSupport C.energy :=
    C.regularXiNonnegativeSquaredSupport_of_faithfulRows h
  exact not_faithful_of_nonrealRegularXiZero hsupport.1 hz hzim hsupport

end Carrier

/-- Existence of a faithful ordinary Fredholm squared carrier. -/
def HasFaithfulFredholmSquaredCarrier : Prop :=
  ∃ C : Carrier.{u}, C.FaithfulRows

/-- A faithful ordinary Fredholm carrier supplies the packaged squared-support
endpoint. -/
theorem nonempty_nonnegativeSquaredSupport_of_hasFaithfulFredholmSquaredCarrier
    (hC : HasFaithfulFredholmSquaredCarrier.{u}) :
    Nonempty RiemannXiNonnegativeSquaredSupport.{u} := by
  rcases hC with ⟨C, hrows⟩
  exact ⟨{
    Spectrum := C.Spectrum
    energy := C.energy
    faithful := C.regularXiNonnegativeSquaredSupport_of_faithfulRows hrows
  }⟩

/-- A faithful ordinary Fredholm squared carrier proves mathlib's RH. -/
theorem riemannHypothesis_of_hasFaithfulFredholmSquaredCarrier
    (hC : HasFaithfulFredholmSquaredCarrier.{u}) :
    RiemannHypothesis := by
  rcases hC with ⟨C, hrows⟩
  exact C.riemannHypothesis_of_faithfulRows hrows

/-!
## Circular calibration

The next definitions show that the abstract carrier boundary has no hidden
strength beyond exact nonnegative squared support.  The reverse direction is a
calibration only: it labels already-faithful squared support with `True`
Fredholm rows and must not be read as constructing `T`.
-/

/-- Calibrate the Fredholm interface against an already faithful nonnegative
squared-support endpoint. -/
def carrierOfNonnegativeSquaredSupport
    (S : RiemannXiNonnegativeSquaredSupport.{u}) :
    Carrier.{u} where
  Spectrum := S.Spectrum
  energy := S.energy
  positiveSquare := True
  traceClassSquare := True
  hilbertSchmidtRoot := True
  fredholmDeterminantIdentity := True
  nonnegative_of_positiveSquare := by
    intro _hpos
    exact S.faithful.1
  complete_of_fredholmRows := by
    intro _htrace _hroot _hdet z hz
    exact S.faithful.2 z hz

/-- The calibrated carrier has faithful rows. -/
theorem faithfulRows_carrierOfNonnegativeSquaredSupport
    (S : RiemannXiNonnegativeSquaredSupport.{u}) :
    (carrierOfNonnegativeSquaredSupport S).FaithfulRows :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Exact nonnegative squared support supplies the calibrated Fredholm carrier. -/
theorem hasFaithfulFredholmSquaredCarrier_of_nonnegativeSquaredSupport
    (S : RiemannXiNonnegativeSquaredSupport.{u}) :
    HasFaithfulFredholmSquaredCarrier.{u} :=
  ⟨carrierOfNonnegativeSquaredSupport S,
    faithfulRows_carrierOfNonnegativeSquaredSupport S⟩

/--
The abstract Fredholm carrier handoff is equivalent to the existing
nonnegative squared-support endpoint.  The reverse direction is the circular
calibration above, not a construction of a Fredholm determinant.
-/
theorem hasFaithfulFredholmSquaredCarrier_iff_nonnegativeSquaredSupport :
    HasFaithfulFredholmSquaredCarrier.{u} ↔
      Nonempty RiemannXiNonnegativeSquaredSupport.{u} := by
  constructor
  · exact nonempty_nonnegativeSquaredSupport_of_hasFaithfulFredholmSquaredCarrier
  · intro hS
    rcases hS with ⟨S⟩
    exact hasFaithfulFredholmSquaredCarrier_of_nonnegativeSquaredSupport S

/-- Circular squared-support endpoint obtained from RH itself. -/
noncomputable def nonnegativeSquaredSupportOfRiemannHypothesis
    (hRH : RiemannHypothesis) :
    RiemannXiNonnegativeSquaredSupport.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXiRegularZero z}
  energy γ := γ.1.re ^ 2
  faithful := by
    constructor
    · intro γ
      exact sq_nonneg γ.1.re
    · intro z hz
      refine ⟨⟨z, hz⟩, ?_⟩
      have him : z.im = 0 :=
        (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1
          hRH z hz
      apply Complex.ext <;> simp [pow_two, him]

/-- RH supplies only the calibrated, circular Fredholm carrier. -/
theorem hasFaithfulFredholmSquaredCarrier_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    HasFaithfulFredholmSquaredCarrier.{0} :=
  hasFaithfulFredholmSquaredCarrier_of_nonnegativeSquaredSupport
    (nonnegativeSquaredSupportOfRiemannHypothesis hRH)

/--
At universe zero, the abstract ordinary Fredholm squared-carrier endpoint has
exactly RH strength.

The useful direction is the conditional carrier theorem.  The reverse direction
is the tautological calibration from already-real regular `Xi` zeros.
-/
theorem hasFaithfulFredholmSquaredCarrier_iff_riemannHypothesis :
    HasFaithfulFredholmSquaredCarrier.{0} ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_hasFaithfulFredholmSquaredCarrier
  · exact hasFaithfulFredholmSquaredCarrier_of_riemannHypothesis

/-- Packaged conditional certificate for the ordinary Fredholm squared route. -/
structure FredholmSquaredRHCertificate where
  carrier : Carrier.{u}
  faithfulRows : carrier.FaithfulRows

namespace FredholmSquaredRHCertificate

/-- The packaged Fredholm squared certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : FredholmSquaredRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.carrier.riemannHypothesis_of_faithfulRows cert.faithfulRows

/-- The packaged certificate supplies exact nonnegative squared support. -/
def nonnegativeSquaredSupport
    (cert : FredholmSquaredRHCertificate.{u}) :
    RiemannXiNonnegativeSquaredSupport.{u} where
  Spectrum := cert.carrier.Spectrum
  energy := cert.carrier.energy
  faithful :=
    cert.carrier.regularXiNonnegativeSquaredSupport_of_faithfulRows
      cert.faithfulRows

end FredholmSquaredRHCertificate

end FredholmSquaredCarrier
end JensenLadder
