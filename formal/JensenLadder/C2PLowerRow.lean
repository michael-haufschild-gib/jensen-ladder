import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# C2P independent lower-row certificate interface

This file packages the ordered-field assembly needed for the C2P lower row

```text
  -Eprime <= Q_{H_B}^xi.
```

It does not prove any analytic Suzuki, Weil, prime, or remainder estimate.  It
only records how finite interval certificates should hand their inequalities to
the comparison-form PacketForce consumer.

## Honest scope

The analytic lower-row constants remain hypotheses.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace C2PLowerRow

/-- A generic lower-row certificate: a certified lower endpoint `LB` lies below
the observable `cmp`, and that endpoint is above the required floor. -/
structure LowerBound where
  cmp : ℝ
  Eprime : ℝ
  LB : ℝ
  hLB : LB ≤ cmp
  hfloorLB : -Eprime ≤ LB

/-- A generic certified lower endpoint supplies the C2P lower row. -/
theorem LowerBound.floor (C : LowerBound) :
    -C.Eprime ≤ C.cmp :=
  le_trans C.hfloorLB C.hLB

/-- A point value with an absolute error bound supplies a lower endpoint
`point - err`. -/
theorem lower_bound_of_abs_error
    {cmp point err : ℝ}
    (herr : |cmp - point| ≤ err) :
    point - err ≤ cmp := by
  rw [abs_le] at herr
  linarith

/-- The common interval-certificate form: if `point` approximates `cmp` within
`err`, and `point - err` is still above the floor, then the lower row holds. -/
theorem floor_of_abs_error
    {cmp point err Eprime : ℝ}
    (herr : |cmp - point| ≤ err)
    (hfloor : -Eprime ≤ point - err) :
    -Eprime ≤ cmp :=
  le_trans hfloor (lower_bound_of_abs_error herr)

/-- A packaged point-plus-error lower-row certificate. -/
structure ApproxLowerBound where
  cmp : ℝ
  point : ℝ
  err : ℝ
  Eprime : ℝ
  herr : |cmp - point| ≤ err
  hfloor : -Eprime ≤ point - err

/-- A point-plus-error certificate supplies the C2P lower row. -/
theorem ApproxLowerBound.floor (C : ApproxLowerBound) :
    -C.Eprime ≤ C.cmp :=
  floor_of_abs_error C.herr C.hfloor

/-- Component bounds for a Suzuki-style full form

```text
  Q = L - A*M - P - R.
```

To lower-bound `Q`, it is enough to supply a lower bound for `L`, upper bounds
for `M`, `P`, and `R`, and nonnegativity of `A`.  This matches the C01 lower-row
interval ledger: `L_h` is a lower interval endpoint, while the subtracted terms
use upper interval endpoints. -/
structure SuzukiComponentBounds where
  Q : ℝ
  Eprime : ℝ
  A : ℝ
  L : ℝ
  M : ℝ
  P : ℝ
  R : ℝ
  Llo : ℝ
  Mhi : ℝ
  Phi : ℝ
  Rhi : ℝ
  hQ : Q = L - A * M - P - R
  hA_nonneg : 0 ≤ A
  hL : Llo ≤ L
  hM : M ≤ Mhi
  hP : P ≤ Phi
  hR : R ≤ Rhi
  hfloor : -Eprime ≤ Llo - A * Mhi - Phi - Rhi

/-- Suzuki component interval bounds assemble into the independent lower row. -/
theorem SuzukiComponentBounds.floor (C : SuzukiComponentBounds) :
    -C.Eprime ≤ C.Q := by
  have hAM : C.A * C.M ≤ C.A * C.Mhi :=
    mul_le_mul_of_nonneg_left C.hM C.hA_nonneg
  rw [C.hQ]
  linarith [C.hfloor, C.hL, C.hP, C.hR, hAM]

end C2PLowerRow
end JensenLadder
