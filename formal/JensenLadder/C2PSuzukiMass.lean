import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum.Basic

/-!
# C2P fixed ScrewHat mass ledger

This file formalizes the exact arithmetic part of the C01 lower-row mass
ledger for the fixed `(a=4, N_mesh=20, ones)` ScrewHat observable.

It proves only the finite tridiagonal mass-matrix arithmetic

```text
  (2h/3) * 19 + (h/3) * 18 = 112/15,   h = 2/5.
```

It does not prove the analytic hat-integral identity that identifies this
finite mass matrix with `int v_*(x)^2 dx`; that remains a separate C01 lemma.

## Honest scope

This is a C5 constant lemma, not an RH proof.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace C2PSuzukiMass

/-- Tridiagonal finite-element hat mass for an all-ones interior coefficient
vector, expressed through the number of diagonal entries and adjacent interior
pairs.  For hats with step `h`, the quadratic form is
`(2h/3) * diagCount + (h/3) * adjacentCount`. -/
noncomputable def tridiagonalHatMass (h : ℝ) (diagCount adjacentCount : ℕ) : ℝ :=
  ((2 * h) / 3) * diagCount + (h / 3) * adjacentCount

/-- The fixed C01 ones vector has mesh step `h = 2/5`. -/
noncomputable def fixedStep : ℝ :=
  (2 : ℝ) / 5

/-- Interior nodes for `(a=4, N_mesh=20)` are `1,...,19`. -/
def fixedInteriorCount : ℕ :=
  19

/-- Adjacent interior pairs for the fixed ones vector are `(1,2),...,(18,19)`. -/
def fixedAdjacentCount : ℕ :=
  18

/-- The fixed C01 tridiagonal mass ledger value. -/
noncomputable def fixedOnesMass : ℝ :=
  tridiagonalHatMass fixedStep fixedInteriorCount fixedAdjacentCount

/-- Exact arithmetic value of the fixed C01 mass ledger. -/
theorem fixedOnesMass_eq :
    fixedOnesMass = (112 : ℝ) / 15 := by
  norm_num [fixedOnesMass, tridiagonalHatMass, fixedStep,
    fixedInteriorCount, fixedAdjacentCount]

/-- The fixed C01 mass ledger is nonnegative. -/
theorem fixedOnesMass_nonneg :
    0 ≤ fixedOnesMass := by
  rw [fixedOnesMass_eq]
  norm_num

/-- The fixed C01 mass ledger is positive. -/
theorem fixedOnesMass_pos :
    0 < fixedOnesMass := by
  rw [fixedOnesMass_eq]
  norm_num

end C2PSuzukiMass
end JensenLadder
