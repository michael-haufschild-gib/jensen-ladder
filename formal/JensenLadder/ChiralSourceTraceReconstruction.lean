import JensenLadder.ChiralSourceMomentGate
import JensenLadder.ChiralMomentReconstruction

/-!
# Chiral source-trace determinant reconstruction

This module packages the finite no-free-factor row for the chiral
prime-cepstrum/Hankel lane.

`ChiralSourceMomentGate` isolates the source-to-moment identity needed for the
Stieltjes PSD tests.  The determinant itself needs a stronger row: the native
completed-source trace must be the same trace as the finite Fredholm determinant
of the positive squared carrier.  Once that trace row is proved on a connected
zero-free domain, `ChiralMomentReconstruction` shows that one basepoint fixes
the determinant; no later zero-free factor may be inserted.

This file does not construct the source trace, the carrier, the fake suite, a
Fredholm determinant library, a limiting determinant theorem, or RH.

Evidence class: formal/certificate artifact; theorem-target refinement.  Theorem
M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ChiralSourceTraceReconstruction

open Set

universe u

/--
A finite source-trace carrier.

`sameCarrierTraceIdentity` is the live CPH-4 row: the declared source trace is
identical to the finite Fredholm Stieltjes trace of the same positive squared
carrier on the declared domain.
-/
structure FiniteSourceTraceCarrier where
  momentCarrier : ChiralSourceMomentGate.FiniteSourceMomentCarrier.{u}
  domain : Set ℂ
  sourceTrace : momentCarrier.Stream -> ℂ -> ℂ
  sameCarrierTraceIdentity : Prop
  sameCarrierTraceIdentity_proves :
    sameCarrierTraceIdentity ->
      EqOn (sourceTrace momentCarrier.source)
        momentCarrier.spectrum.fredholmResolventTrace domain

namespace FiniteSourceTraceCarrier

/-- The live source-trace row. -/
def LiveTraceRow (C : FiniteSourceTraceCarrier.{u}) : Prop :=
  C.sameCarrierTraceIdentity

/--
A diagnostic source-moment carrier with no live source-trace identity.
-/
def diagnosticOnly : FiniteSourceTraceCarrier.{0} where
  momentCarrier := ChiralSourceMomentGate.FiniteSourceMomentCarrier.diagnosticOnly
  domain := Set.univ
  sourceTrace := fun _ _ => 0
  sameCarrierTraceIdentity := False
  sameCarrierTraceIdentity_proves := by
    intro hfalse
    cases hfalse

/--
Moment diagnostics alone do not supply the live source-trace identity.
-/
theorem diagnostics_do_not_supply_liveTraceRow :
    ∃ C : FiniteSourceTraceCarrier.{0},
      C.momentCarrier.DiagnosticRows ∧ ¬ C.LiveTraceRow :=
  ⟨diagnosticOnly, ⟨trivial, trivial⟩, by
    intro hfalse
    exact hfalse⟩

/--
If the source trace is native to the same finite carrier and a target has that
same source trace, then the target has the finite Fredholm determinant trace.
-/
theorem target_trace_eq_fredholmTrace
    (C : FiniteSourceTraceCarrier.{u})
    (hsource : C.sameCarrierTraceIdentity)
    {target : ℂ -> ℂ}
    (htarget :
      EqOn (fun z => -logDeriv target z)
        (C.sourceTrace C.momentCarrier.source) C.domain) :
    EqOn (fun z => -logDeriv target z)
      C.momentCarrier.spectrum.fredholmResolventTrace C.domain := by
  intro z hz
  exact (htarget hz).trans (C.sameCarrierTraceIdentity_proves hsource hz)

/--
Finite same-source trace reconstruction: on a connected zero-free domain, the
same-carrier source trace plus one basepoint identifies the target with the
finite Fredholm determinant.
-/
theorem fredholmDeterminant_eqOn_target_of_sourceTrace_and_basepoint
    (C : FiniteSourceTraceCarrier.{u})
    (hsource : C.sameCarrierTraceIdentity)
    {target : ℂ -> ℂ} {z0 : ℂ}
    (htarget : DifferentiableOn ℂ target C.domain)
    (hopen : IsOpen C.domain)
    (hconn : IsPreconnected C.domain)
    (hoff : ∀ z ∈ C.domain, C.momentCarrier.spectrum.FredholmOffSpectrum z)
    (htarget_ne : ∀ z ∈ C.domain, target z ≠ 0)
    (htarget_trace :
      EqOn (fun z => -logDeriv target z)
        (C.sourceTrace C.momentCarrier.source) C.domain)
    (hz0 : z0 ∈ C.domain)
    (hbase :
      C.momentCarrier.spectrum.fredholmDeterminant z0 = target z0) :
    EqOn C.momentCarrier.spectrum.fredholmDeterminant target C.domain :=
  C.momentCarrier.spectrum.fredholmDeterminant_eqOn_of_same_trace_and_basepoint
    htarget hopen hconn hoff htarget_ne
    (C.target_trace_eq_fredholmTrace hsource htarget_trace)
    hz0 hbase

end FiniteSourceTraceCarrier

/-- Packaged finite source trace reconstruction certificate. -/
structure SourceTraceReconstructionCertificate where
  carrier : FiniteSourceTraceCarrier.{u}
  sameCarrierTraceIdentity : carrier.sameCarrierTraceIdentity

namespace SourceTraceReconstructionCertificate

/--
The packaged source trace certificate reconstructs the finite Fredholm
determinant from a target source-trace row and a basepoint.
-/
theorem fredholmDeterminant_eqOn_target
    (cert : SourceTraceReconstructionCertificate.{u})
    {target : ℂ -> ℂ} {z0 : ℂ}
    (htarget : DifferentiableOn ℂ target cert.carrier.domain)
    (hopen : IsOpen cert.carrier.domain)
    (hconn : IsPreconnected cert.carrier.domain)
    (hoff : ∀ z ∈ cert.carrier.domain,
      cert.carrier.momentCarrier.spectrum.FredholmOffSpectrum z)
    (htarget_ne : ∀ z ∈ cert.carrier.domain, target z ≠ 0)
    (htarget_trace :
      EqOn (fun z => -logDeriv target z)
        (cert.carrier.sourceTrace cert.carrier.momentCarrier.source)
        cert.carrier.domain)
    (hz0 : z0 ∈ cert.carrier.domain)
    (hbase :
      cert.carrier.momentCarrier.spectrum.fredholmDeterminant z0 = target z0) :
    EqOn cert.carrier.momentCarrier.spectrum.fredholmDeterminant target
      cert.carrier.domain :=
  cert.carrier.fredholmDeterminant_eqOn_target_of_sourceTrace_and_basepoint
    cert.sameCarrierTraceIdentity htarget hopen hconn hoff htarget_ne
    htarget_trace hz0 hbase

end SourceTraceReconstructionCertificate

end ChiralSourceTraceReconstruction
end JensenLadder
