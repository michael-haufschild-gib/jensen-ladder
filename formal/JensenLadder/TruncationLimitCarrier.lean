import JensenLadder.FiniteCarrierNoGo
import JensenLadder.SpectralRealization

/-!
# Truncation-limit carrier boundary

`FiniteCarrierNoGo` rules out a literal finite exact carrier for the full `Xi`
zero multiset.  This file records the corrected finite-truncation target:
a family of finite spectral truncations can hand off to RH only after an
exhaustion theorem says that every regular `Xi` zero occurs at some scale.

The per-scale finiteness field is deliberately present but proof-irrelevant for
the RH handoff.  It marks the intended shape of a truncation program.  The
load-bearing row is `Family.Exhaustive`.

This module does not construct a truncation family, prove convergence, prove
Riemann--von Mangoldt, prove RH, or refute RH.  It only formalizes the exact
limit/exhaustion row needed after the finite-carrier no-go.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace TruncationLimitCarrier

open SpectralRealization

universe u

/--
A family of finite spectral truncations.

`Scale` indexes the truncations, `Slot a` is the finite spectral list at scale
`a`, and `height` assigns real heights to all slots in the total sigma carrier.
The `sound` row prevents extra truncation slots from being treated as `Xi`
zeros.  Completeness is intentionally not a field; it is the separate
`Family.Exhaustive` row below.
-/
structure Family where
  Scale : Type u
  Slot : Scale -> Type u
  finiteSlot : ∀ a : Scale, Finite (Slot a)
  height : (Σ a : Scale, Slot a) -> ℝ
  sound : ∀ p : (Σ a : Scale, Slot a),
    RHReduction.riemannXiRegularZero (height p : ℂ)

namespace Family

/--
The limiting/exhaustion theorem required by a finite-truncation program:
every regular `Xi` zero appears in some finite truncation slot.
-/
def Exhaustive (F : Family.{u}) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
    ∃ p : (Σ a : F.Scale, F.Slot a), z = (F.height p : ℂ)

/-- A regular `Xi` zero missed by every truncation slot. -/
def MissingRegularXiZero (F : Family.{u}) : Prop :=
  ∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧
    ∀ p : (Σ a : F.Scale, F.Slot a), z ≠ (F.height p : ℂ)

/-- Exhaustion rules out missing regular `Xi` zeros. -/
theorem no_missingRegularXiZero_of_exhaustive
    (F : Family.{u})
    (hexhaustive : F.Exhaustive) :
    ¬ F.MissingRegularXiZero := by
  intro hmiss
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases hexhaustive z hz with ⟨p, hp⟩
  exact hmissing p hp

/-- A missed regular zero blocks the exhaustion row. -/
theorem not_exhaustive_of_missingRegularXiZero
    (F : Family.{u})
    (hmiss : F.MissingRegularXiZero) :
    ¬ F.Exhaustive := by
  intro hexhaustive
  exact no_missingRegularXiZero_of_exhaustive F hexhaustive hmiss

/--
An exhaustive truncation family packages into the existing exact regular
spectral-realization endpoint.
-/
def regularSpectralRealization_of_exhaustive
    (F : Family.{u})
    (hexhaustive : F.Exhaustive) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := Σ a : F.Scale, F.Slot a
  height := F.height
  sound := F.sound
  complete := hexhaustive

/--
An exhaustive finite-truncation family would prove mathlib's
`RiemannHypothesis`.

This is not a proof of RH.  The hard input is the exhaustion/convergence row
`Family.Exhaustive`.
-/
theorem riemannHypothesis_of_exhaustive
    (F : Family.{u})
    (hexhaustive : F.Exhaustive) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_exhaustive F hexhaustive)

/-- A non-real regular `Xi` zero is missed by every real-height truncation slot. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (F : Family.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    F.MissingRegularXiZero := by
  refine ⟨z, hz, ?_⟩
  intro p hp
  exact hzim (by
    rw [hp]
    simp)

/-- A non-real regular `Xi` zero blocks the exhaustion row. -/
theorem not_exhaustive_of_nonrealRegularXiZero
    (F : Family.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ F.Exhaustive :=
  not_exhaustive_of_missingRegularXiZero F
    (missingRegularXiZero_of_nonrealRegularXiZero F hz hzim)

end Family

/-- Packaged conditional certificate for the finite-truncation limit route. -/
structure TruncationLimitRHCertificate where
  family : Family.{u}
  exhaustive : family.Exhaustive

namespace TruncationLimitRHCertificate

/-- The packaged certificate supplies the regular spectral-realization endpoint. -/
def regularSpectralRealization
    (C : TruncationLimitRHCertificate.{u}) :
    RiemannXiRegularSpectralRealization.{u} :=
  C.family.regularSpectralRealization_of_exhaustive C.exhaustive

/-- The packaged truncation-limit certificate proves mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis
    (C : TruncationLimitRHCertificate.{u}) :
    RiemannHypothesis :=
  C.family.riemannHypothesis_of_exhaustive C.exhaustive

end TruncationLimitRHCertificate

end TruncationLimitCarrier
end JensenLadder
