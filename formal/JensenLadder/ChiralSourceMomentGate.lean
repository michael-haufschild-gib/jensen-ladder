import JensenLadder.ChiralMomentPSD

/-!
# Chiral source-to-moment gate

This module records the finite source-to-Stieltjes row for the chiral
prime-cepstrum/Hankel lane.

The existing `ChiralMomentPSD` file proves that moments native to a finite
nonnegative squared spectrum have the two standard Stieltjes Hankel PSD
certificates.  The load-bearing CPH row is therefore not PSD itself, but the
same-carrier identity saying that the completed explicit-formula source moments
are exactly those finite spectral moments.

This file packages that handoff:

* a source moment functional becomes Stieltjes-positive once it is proved equal
  to the same carrier's finite `T*T` moments;
* zero-side and `Xi`-Taylor diagnostics do not supply that source identity;
* fake-family screening must fail at a named row, not merely at the final zero
  comparison.

It does not construct the source stream, the finite basis, `T`, fake streams,
determinant convergence, or RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ChiralSourceMomentGate

open scoped BigOperators

universe u

/--
A finite source-moment carrier.

`momentFunctional` is the declared completed-source moment row.  The key live
row is `sameCarrierMomentIdentity`: once proved, it identifies that source row
with the moments of the same finite nonnegative squared spectrum.
-/
structure FiniteSourceMomentCarrier where
  Stream : Type u
  source : Stream
  spectrum : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.{u}
  momentFunctional : Stream -> ℕ -> ℝ
  zeroSideMomentDiagnostics : Prop
  xiTaylorMomentDiagnostics : Prop
  sameCarrierMomentIdentity : Prop
  sameCarrierMomentIdentity_proves :
    sameCarrierMomentIdentity ->
      ∀ k : ℕ, momentFunctional source k = spectrum.moment k

namespace FiniteSourceMomentCarrier

/-- Diagnostic rows are useful screens, but they are not source-carrier data. -/
def DiagnosticRows (C : FiniteSourceMomentCarrier.{u}) : Prop :=
  C.zeroSideMomentDiagnostics ∧ C.xiTaylorMomentDiagnostics

/-- The live source-to-moment row. -/
def LiveSourceRow (C : FiniteSourceMomentCarrier.{u}) : Prop :=
  C.sameCarrierMomentIdentity

/-- The shifted Hankel quadratic form built from an arbitrary declared stream. -/
noncomputable def sourceHankelQuadratic
    (C : FiniteSourceMomentCarrier.{u}) (stream : C.Stream)
    (shift n : ℕ) (c : Fin n -> ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    c i * c j * C.momentFunctional stream (shift + i.val + j.val)

/--
Once the same-carrier source identity is proved, source Hankel forms are the
finite spectral Hankel forms from the positive squared carrier.
-/
theorem sourceHankelQuadratic_eq_spectral
    (C : FiniteSourceMomentCarrier.{u})
    (hsource : C.sameCarrierMomentIdentity)
    (shift n : ℕ) (c : Fin n -> ℝ) :
    C.sourceHankelQuadratic C.source shift n c =
      C.spectrum.hankelQuadratic shift n c := by
  have hmom := C.sameCarrierMomentIdentity_proves hsource
  simp [sourceHankelQuadratic,
    SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.hankelQuadratic,
    hmom]

/--
Same-carrier source moments inherit the finite Stieltjes/Hankel PSD certificate.
-/
theorem sourceHankelQuadratic_nonnegative
    (C : FiniteSourceMomentCarrier.{u})
    (hsource : C.sameCarrierMomentIdentity)
    (shift n : ℕ) (c : Fin n -> ℝ) :
    0 <= C.sourceHankelQuadratic C.source shift n c := by
  rw [C.sourceHankelQuadratic_eq_spectral hsource shift n c]
  exact C.spectrum.hankelQuadratic_nonnegative shift n c

/--
The two standard Stieltjes tests for the completed source moments, after the
same-carrier identity has been proved.
-/
theorem sourceStieltjesHankelPair_nonnegative
    (C : FiniteSourceMomentCarrier.{u})
    (hsource : C.sameCarrierMomentIdentity)
    (n : ℕ) (c0 c1 : Fin n -> ℝ) :
    0 <= C.sourceHankelQuadratic C.source 0 n c0 ∧
      0 <= C.sourceHankelQuadratic C.source 1 n c1 :=
  ⟨C.sourceHankelQuadratic_nonnegative hsource 0 n c0,
    C.sourceHankelQuadratic_nonnegative hsource 1 n c1⟩

/-- An empty finite positive squared spectrum for diagnostic calibration. -/
def emptySpectrum : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.{0} where
  Index := Empty
  fintype := inferInstance
  energy := fun i => nomatch i
  nonnegative := by
    intro i
    cases i

/--
A carrier with diagnostic moment rows but no same-source identity.

This is a calibration object: it shows that zero-side and `Xi`-Taylor moment
screens are not proof input by themselves.
-/
def diagnosticOnly : FiniteSourceMomentCarrier.{0} where
  Stream := PUnit
  source := PUnit.unit
  spectrum := emptySpectrum
  momentFunctional := fun _ _ => 0
  zeroSideMomentDiagnostics := True
  xiTaylorMomentDiagnostics := True
  sameCarrierMomentIdentity := False
  sameCarrierMomentIdentity_proves := by
    intro hfalse
    cases hfalse

/--
Diagnostic zero-side and `Xi`-Taylor moment rows do not supply the live
same-carrier source identity.
-/
theorem diagnosticRows_do_not_supply_liveSourceRow :
    ∃ C : FiniteSourceMomentCarrier.{0}, C.DiagnosticRows ∧ ¬ C.LiveSourceRow :=
  ⟨diagnosticOnly, ⟨trivial, trivial⟩, by
    intro hfalse
    exact hfalse⟩

end FiniteSourceMomentCarrier

/-!
## Named fake-family failure rows
-/

/--
The named rows at which a fake stream may fail the source-to-moment packet.

These are the finite Lean names for FM1--FM5 in the source-to-moment gate note.
-/
structure FakeFailureRows where
  sourceSupportFailure : Prop
  momentSignFailure : Prop
  stieltjesSupportFailure : Prop
  residualSelectorFailure : Prop
  cofinalityFailure : Prop

namespace FakeFailureRows

/-- The fake stream fails at at least one named row. -/
def Holds (R : FakeFailureRows) : Prop :=
  R.sourceSupportFailure ∨
    R.momentSignFailure ∨
      R.stieltjesSupportFailure ∨
        R.residualSelectorFailure ∨
          R.cofinalityFailure

/-- Fake-blind rows: no named source, moment, Stieltjes, selector, or cofinality failure. -/
def fakeBlind : FakeFailureRows where
  sourceSupportFailure := False
  momentSignFailure := False
  stieltjesSupportFailure := False
  residualSelectorFailure := False
  cofinalityFailure := False

/-- A fake-blind row package does not satisfy the named-failure requirement. -/
theorem not_holds_fakeBlind : ¬ fakeBlind.Holds := by
  intro h
  rcases h with h | h | h | h | h <;> exact h

end FakeFailureRows

/-- Every fake in a declared fake suite fails at a named structural row. -/
def AllFakesFailAtNamedRow (Fake : Type u) (rows : Fake -> FakeFailureRows) : Prop :=
  ∀ f : Fake, (rows f).Holds

/--
If a nonempty fake suite is fake-blind at every row, it cannot satisfy the
named-failure gate.
-/
theorem not_allFakesFailAtNamedRow_of_fakeBlind
    {Fake : Type u} [Nonempty Fake] {rows : Fake -> FakeFailureRows}
    (hblind : ∀ f : Fake, rows f = FakeFailureRows.fakeBlind) :
    ¬ AllFakesFailAtNamedRow Fake rows := by
  intro hall
  rcases (inferInstance : Nonempty Fake) with ⟨f⟩
  have hf : (rows f).Holds := hall f
  rw [hblind f] at hf
  exact FakeFailureRows.not_holds_fakeBlind hf

/-- Packaged finite source-to-Stieltjes certificate. -/
structure SourceToStieltjesCertificate where
  carrier : FiniteSourceMomentCarrier.{u}
  sameCarrierMomentIdentity : carrier.sameCarrierMomentIdentity

namespace SourceToStieltjesCertificate

/-- A packaged source certificate supplies the ordinary and shifted Hankel PSD rows. -/
theorem sourceStieltjesHankelPair_nonnegative
    (cert : SourceToStieltjesCertificate.{u})
    (n : ℕ) (c0 c1 : Fin n -> ℝ) :
    0 <= cert.carrier.sourceHankelQuadratic cert.carrier.source 0 n c0 ∧
      0 <= cert.carrier.sourceHankelQuadratic cert.carrier.source 1 n c1 :=
  cert.carrier.sourceStieltjesHankelPair_nonnegative
    cert.sameCarrierMomentIdentity n c0 c1

end SourceToStieltjesCertificate

end ChiralSourceMomentGate
end JensenLadder
