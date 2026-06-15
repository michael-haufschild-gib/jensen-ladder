import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# W3 inner-factor consumer (operator-norm ⟹ no fixed eigenvalue) — RH-EQUIVALENT HYPOTHESIS

This is the **consumer half** of the strong-identity wall **W3** in the carrier/`det_reg = Ξ` program
(opus's grand unification §5.15; requested in opus msg-82b057f2, 2026-06-15). In the
Szegő–Widom / BOGC picture, `Ξ = G(φ_s) · det(1 − H(b_s) H(c_s))`, and the RH content is

  **W3: `‖H(b_s) H(c_s)‖ < 1` on `Re s > ½`** (inner-factor triviality / no spurious determinant zero).

The lemmas below are the *consumer*: from the operator-norm bound `‖A‖ < 1` they conclude `1 ∉ spec A`,
hence `1 − A` is invertible and the cross-Hankel determinant `det(1 − A)` does not vanish (no inner
factor). This is **pure operator theory (a Neumann-series fact), RH-agnostic**.

**⚠ The HYPOTHESIS `‖A‖ < 1` on `Re s > ½` is itself RH-EQUIVALENT and is NOT proved here.** It is the
W3 wall: assuming it on the open right half-plane would assume RH. Per opus's instruction this consumer
must be PAIRED with meister's `INNER-FACTOR-OVERCLAIM-FALSIFIER` (§51,
`docs/rh/meister_nonscalar_carrier_reduction_20260614.md`) — i.e. the hypothesis must be discharged by
genuine W3 input (arithmetic Hodge-index / Yuan–Zhang positivity), never silently. **Theorem M is
proven, but Theorem M does not prove RH by itself; this file proves no RH content.**
-/

open scoped Topology

namespace W3InnerFactor

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Neumann consumer:** an operator-norm contraction `‖a‖ < 1` makes `1 − a` invertible. RH-agnostic
(Neumann series); the RH content is entirely in establishing the hypothesis `‖a‖ < 1`. -/
theorem isUnit_one_sub_of_op_norm_lt_one {a : A} (h : ‖a‖ < 1) : IsUnit (1 - a) :=
  isUnit_one_sub_of_norm_lt_one h

/-- **W3 inner-factor consumer:** if the cross-Hankel operator `a` satisfies `‖a‖ < 1`, then `1` is not
in its spectrum — equivalently `1 − a` is invertible, so the determinant `det(1 − a)` is non-vanishing
and contributes no inner factor / spurious zero. The hypothesis `‖a‖ < 1` on `Re s > ½` is the
RH-EQUIVALENT wall W3 (NOT proved). -/
theorem one_notMem_spectrum_of_op_norm_lt_one {a : A} (h : ‖a‖ < 1) :
    (1 : ℂ) ∉ spectrum ℂ a := by
  rw [spectrum.mem_iff, not_not, map_one]
  exact isUnit_one_sub_of_norm_lt_one h

end W3InnerFactor
