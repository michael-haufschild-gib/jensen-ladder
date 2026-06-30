import Mathlib
import JensenLadder.T3T5Stage0Package

/-!
# Stage 3 of the T3/T5 program: the self-intersection functional and the fake-family referee

Stage 3 of `docs/plans/program_T3_T5_self_product_construction_20260617.md` asks for the
self-product's intersection form `Tr(Δ·Γ) = ` the Weil explicit-formula functional, with a
**non-circularity referee** (T9 fake filter): a valid self-product must reject the
Davenport–Heilbronn fake (`Q_DH = −0.483 < 0`).

This module formalizes the **referee** at the level of the d=2 Lefschetz package
(`T3T5Stage0.LefschetzD2`).  The pod computation `dyson_critical_coupling_attempt_20260618`
identified the package concretely in the CCM operator: the intersection form is
`Q = W_R + P` (archimedean correction + prime, even sector), and the Weil form is
`QW = W0_2 − Q`.  For ζ, `Q` is Lorentzian `(1, N−1)` (one positive = the ample/Lefschetz
direction `L ≈ ` the archimedean `u`-mode); for **DH** it is `(+7, −6)` — it has **extra
positive directions in the primitive part**, i.e. a primitive vector `v` with `Q(v,v) > 0`.

The referee formalized here: **a positive primitive direction falsifies Hodge–Riemann**
(`not_hodgeRiemann_of_positive_primitive`).  This is the exact mechanism by which a
non-Lorentzian (fake) intersection form is rejected — the DH form has such a `v`, ζ does not.
Combined with `PrimeResonanceFreeness` (the firewall: ζ's primes have no exact resonance, so
no spurious positive directions; fakes can), it is the non-circular fake filter.

`selfIntersection` is the degree-2 self-pairing `x ↦ Q(x,x)` (the "Lefschetz number /
Weil functional" readout).  Evidence class: linear algebra, axiom-clean.  Does NOT construct
the self-product correspondence `Γ_q` (the open `[C]`), and does NOT prove RH.
-/

namespace JensenLadder
namespace T3T5Stage3

open Matrix
open scoped Matrix
open T3T5Stage0

variable {ι : Type*} [Fintype ι]

/-- The degree-2 self-intersection functional `x ↦ Q(x,x)` (the Lefschetz-number /
Weil-functional readout of the self-product's diagonal). -/
def selfIntersection (P : LefschetzD2 ι) (x : ι → ℝ) : ℝ := x ⬝ᵥ P.Q *ᵥ x

/-- A **primitive** vector for the package: `Q`-orthogonal to the Lefschetz class `L`. -/
def IsPrimitive (P : LefschetzD2 ι) (x : ι → ℝ) : Prop := P.L ⬝ᵥ P.Q *ᵥ x = 0

/-- **Stage-3 fake-family referee.**  A *positive primitive direction* falsifies
Hodge–Riemann: if `v` is primitive (`Q(L,v)=0`) and has positive self-intersection
(`Q(v,v) > 0`), then the package does NOT satisfy Hodge–Riemann.  This is the mechanism
that rejects the Davenport–Heilbronn fake, whose intersection form `W_R+P` carries extra
positive primitive directions (computed signature `(+7,−6)`), while ζ's is Lorentzian
`(1, N−1)` (no positive primitive directions). -/
theorem not_hodgeRiemann_of_positive_primitive (P : LefschetzD2 ι) (v : ι → ℝ)
    (hperp : IsPrimitive P v) (hpos : 0 < selfIntersection P v) :
    ¬ P.HodgeRiemann := by
  intro hHR
  have := hHR v hperp
  exact absurd this (not_le.mpr hpos)

/-- Contrapositive packaging: under Hodge–Riemann, every primitive direction has
nonpositive self-intersection (no fake positive primitive survives). -/
theorem selfIntersection_nonpos_of_hodgeRiemann_primitive (P : LefschetzD2 ι)
    (hHR : P.HodgeRiemann) (v : ι → ℝ) (hperp : IsPrimitive P v) :
    selfIntersection P v ≤ 0 :=
  hHR v hperp

end T3T5Stage3
end JensenLadder
