import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite semilocal Weil matrix interface

This module records the finite matrix shape used by the CCM/Sonin/prolate
numerical harness:

```text
QW[n,m] = W0_2[n,m] - W_R[n,m]
          - sum_{2 <= k <= lambda^2} c_k q_k[n,m].
```

The coefficients `c_k` are already normalized in the caller; for the zeta
harness they are `Lambda(k) / sqrt(k)`.  The file proves only elementary finite
algebra about this split, including the symmetry condition needed before a
finite matrix can be read as a self-adjoint operator.

It does not prove positivity, simplicity of the bottom eigenvalue, convergence
to `Xi`, or the Riemann Hypothesis.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMFiniteWeil

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {ι κ R : Type*} [Fintype κ] [CommRing R]

/-- Finite semilocal Weil matrix data.  `ι` indexes the matrix coordinates and
`κ` indexes the finite prime/local perturbation rows. -/
structure SemilocalFiniteWeilData (ι κ R : Type*) where
  archBase : ι → ι → R
  archTrace : ι → ι → R
  primeCoeff : κ → R
  primeKernel : κ → ι → ι → R

variable (D : SemilocalFiniteWeilData ι κ R)

/-- The archimedean part of the finite Weil matrix. -/
def archPart (i j : ι) : R :=
  D.archBase i j - D.archTrace i j

/-- The finite prime/local perturbation part of the finite Weil matrix. -/
noncomputable def primePart (i j : ι) : R :=
  ∑ q : κ, D.primeCoeff q * D.primeKernel q i j

/-- The finite semilocal Weil matrix entry. -/
noncomputable def entry (i j : ι) : R :=
  archPart D i j - primePart D i j

/-- Expanded form of the finite semilocal Weil matrix entry. -/
theorem entry_eq
    (i j : ι) :
    entry D i j =
      D.archBase i j - D.archTrace i j -
        ∑ q : κ, D.primeCoeff q * D.primeKernel q i j := by
  rfl

/-- If all prime/local coefficients vanish, the semilocal entry is just the
archimedean part. -/
theorem entry_eq_archPart_of_primeCoeff_zero
    (hcoeff : ∀ q : κ, D.primeCoeff q = 0)
    (i j : ι) :
    entry D i j = archPart D i j := by
  simp [entry, primePart, hcoeff]

/-- The finite prime perturbation is symmetric when every local kernel is
symmetric. -/
theorem primePart_swap_eq_of_primeKernel_symmetric
    (hprime : ∀ q : κ, ∀ i j : ι,
      D.primeKernel q i j = D.primeKernel q j i)
    (i j : ι) :
    primePart D i j = primePart D j i := by
  simp [primePart, hprime]

/-- The archimedean part is symmetric when both archimedean rows are symmetric. -/
theorem archPart_swap_eq_of_arch_symmetric
    (hbase : ∀ i j : ι, D.archBase i j = D.archBase j i)
    (htrace : ∀ i j : ι, D.archTrace i j = D.archTrace j i)
    (i j : ι) :
    archPart D i j = archPart D j i := by
  simp [archPart, hbase, htrace]

/-- The finite semilocal Weil matrix is symmetric when its archimedean rows and
each prime/local kernel are symmetric. -/
theorem entry_swap_eq_of_symmetric
    (hbase : ∀ i j : ι, D.archBase i j = D.archBase j i)
    (htrace : ∀ i j : ι, D.archTrace i j = D.archTrace j i)
    (hprime : ∀ q : κ, ∀ i j : ι,
      D.primeKernel q i j = D.primeKernel q j i)
    (i j : ι) :
    entry D i j = entry D j i := by
  simp [entry,
    archPart_swap_eq_of_arch_symmetric D hbase htrace i j,
    primePart_swap_eq_of_primeKernel_symmetric D hprime i j]

/-- A single local row of the finite prime perturbation. -/
def primeRow (q : κ) (i j : ι) : R :=
  D.primeCoeff q * D.primeKernel q i j

/-- The prime perturbation is the sum of its local rows. -/
theorem primePart_eq_sum_primeRow
    (i j : ι) :
    primePart D i j = ∑ q : κ, primeRow D q i j := by
  rfl

/-- Pointwise equality of normalized prime coefficients and local kernels gives
pointwise equality of the finite semilocal Weil entry. -/
theorem entry_eq_of_components_eq
    {D₁ D₂ : SemilocalFiniteWeilData ι κ R}
    (hbase : ∀ i j : ι, D₁.archBase i j = D₂.archBase i j)
    (htrace : ∀ i j : ι, D₁.archTrace i j = D₂.archTrace i j)
    (hcoeff : ∀ q : κ, D₁.primeCoeff q = D₂.primeCoeff q)
    (hkernel : ∀ q : κ, ∀ i j : ι,
      D₁.primeKernel q i j = D₂.primeKernel q i j)
    (i j : ι) :
    entry D₁ i j = entry D₂ i j := by
  simp [entry, archPart, primePart, hbase, htrace, hcoeff, hkernel]

end CCMFiniteWeil
end JensenLadder
