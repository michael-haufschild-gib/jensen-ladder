import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite rank-one algebra for the CCM scaling perturbation

This module formalizes the elementary finite-dimensional algebra behind the
Connes--Consani--Moscovici rank-one perturbation

```text
D' = diag(a_j) - |diag(a_j) xi'><one|.
```

It proves that, when the boundary functional sums `xi'` to `1`, the perturbation
kills `xi'` and agrees with the unperturbed diagonal operator on the boundary
kernel.  This is only the finite algebraic brick.  It does **not** prove the
Riemann Hypothesis, the CCM `N,lambda -> infinity` convergence theorem,
self-adjointness of the analytic Weil-form operator, or any spectral
approximation claim.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMRankOne

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The CCM boundary functional on a finite coefficient block: pairing with the
all-ones vector `one = (1,...,1)`. -/
noncomputable def boundaryFunctional (v : ι → R) : R :=
  ∑ i, v i

/-- The unperturbed finite diagonal part of the scaling operator. -/
def scalingDiagonal (a v : ι → R) : ι → R :=
  fun i => a i * v i

/-- The component of `v` in the boundary kernel after subtracting its boundary
mass in the normalized direction `xi`. -/
noncomputable def kernelPart (xi v : ι → R) : ι → R :=
  fun i => v i - boundaryFunctional v * xi i

/-- The finite rank-one representative
`diag(a) - |diag(a) xi><one|`. -/
noncomputable def rankOnePerturbation (a xi v : ι → R) : ι → R :=
  fun i => scalingDiagonal a v i - boundaryFunctional v * scalingDiagonal a xi i

/-- The kernel decomposition really lands in the boundary kernel when
`boundaryFunctional xi = 1`. -/
theorem boundaryFunctional_kernelPart
    {xi v : ι → R}
    (hxi : boundaryFunctional xi = 1) :
    boundaryFunctional (kernelPart xi v) = 0 := by
  calc
    boundaryFunctional (kernelPart xi v)
        = boundaryFunctional v - boundaryFunctional v * boundaryFunctional xi := by
            simp [boundaryFunctional, kernelPart, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = boundaryFunctional v - boundaryFunctional v * 1 := by rw [hxi]
    _ = 0 := by ring

/-- Subtracting the boundary-kernel component and the normalized boundary
direction recovers the original vector. -/
theorem kernelPart_add_boundary
    (xi v : ι → R) (i : ι) :
    kernelPart xi v i + boundaryFunctional v * xi i = v i := by
  simp [kernelPart]

/-- If a vector is already in the boundary kernel, its kernel part is itself. -/
theorem kernelPart_eq_self_of_boundary_zero
    {xi v : ι → R}
    (hv : boundaryFunctional v = 0) :
    kernelPart xi v = v := by
  ext i
  simp [kernelPart, hv]

/-- The rank-one perturbation kills the normalized vector `xi`. -/
theorem rankOnePerturbation_kills_normalized_vector
    {a xi : ι → R}
    (hxi : boundaryFunctional xi = 1) :
    rankOnePerturbation a xi xi = 0 := by
  ext i
  simp [rankOnePerturbation, scalingDiagonal, hxi]

/-- On the boundary kernel, the rank-one perturbation agrees with the
unperturbed diagonal operator. -/
theorem rankOnePerturbation_agrees_on_boundary_kernel
    {a xi v : ι → R}
    (hv : boundaryFunctional v = 0) :
    rankOnePerturbation a xi v = scalingDiagonal a v := by
  ext i
  simp [rankOnePerturbation, scalingDiagonal, hv]

/-- Equivalently, on an arbitrary vector the rank-one perturbation is the
diagonal operator applied to the boundary-kernel component. -/
theorem rankOnePerturbation_eq_scalingDiagonal_kernelPart
    (a xi v : ι → R) :
    rankOnePerturbation a xi v = scalingDiagonal a (kernelPart xi v) := by
  ext i
  simp [rankOnePerturbation, scalingDiagonal, kernelPart]
  ring

/-- The boundary-kernel predicate for the CCM boundary functional. -/
def BoundaryKernel (v : ι → R) : Prop :=
  boundaryFunctional v = 0

/-- A vector whose boundary functional is normalized to one. -/
def NormalizedBoundaryVector (xi : ι → R) : Prop :=
  boundaryFunctional xi = 1

/-- Pointwise eigen-relation for finite-function operators.

This intentionally carries no `v ≠ 0` side condition; it records the algebraic
relation used by the rank-one perturbation split. -/
def EigenRelation (T : (ι → R) → ι → R) (eigenvalue : R) (v : ι → R) : Prop :=
  T v = fun i => eigenvalue * v i

/-- With a normalized boundary direction, `kernelPart` lands in the boundary
kernel. -/
theorem kernelPart_mem_boundaryKernel
    {xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    BoundaryKernel (kernelPart xi v) := by
  simpa [BoundaryKernel, NormalizedBoundaryVector] using
    (boundaryFunctional_kernelPart (xi := xi) (v := v) hxi)

/-- For a normalized boundary direction, `kernelPart` is idempotent. -/
theorem kernelPart_idempotent
    {xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    kernelPart xi (kernelPart xi v) = kernelPart xi v := by
  exact kernelPart_eq_self_of_boundary_zero
    (xi := xi) (v := kernelPart xi v)
    (by
      simpa [BoundaryKernel] using
        (kernelPart_mem_boundaryKernel (xi := xi) (v := v) hxi))

/-- The normalized boundary direction has zero boundary-kernel component. -/
theorem kernelPart_normalized_vector_eq_zero
    {xi : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    kernelPart xi xi = 0 := by
  ext i
  dsimp [kernelPart, NormalizedBoundaryVector] at hxi ⊢
  rw [hxi]
  ring

/-- The killed normalized direction satisfies the zero eigen-relation for the
rank-one perturbation. -/
theorem rankOnePerturbation_zero_eigenRelation_of_normalized
    {a xi : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    EigenRelation (rankOnePerturbation a xi) 0 xi := by
  dsimp [EigenRelation]
  rw [rankOnePerturbation_kills_normalized_vector
    (a := a) (xi := xi) (by simpa [NormalizedBoundaryVector] using hxi)]
  ext i
  simp

/-- On the boundary kernel, the rank-one perturbation preserves every
pointwise eigen-relation of the unperturbed scaling diagonal. -/
theorem rankOnePerturbation_eigenRelation_of_boundaryKernel
    {a xi v : ι → R} {eigenvalue : R}
    (hv : BoundaryKernel v)
    (heig : EigenRelation (scalingDiagonal a) eigenvalue v) :
    EigenRelation (rankOnePerturbation a xi) eigenvalue v := by
  dsimp [EigenRelation] at heig ⊢
  rw [rankOnePerturbation_agrees_on_boundary_kernel
    (a := a) (xi := xi) (v := v) (by simpa [BoundaryKernel] using hv)]
  exact heig

/-- On the boundary kernel, eigen-relations for the rank-one perturbation and
the unperturbed diagonal are equivalent. -/
theorem rankOnePerturbation_eigenRelation_iff_scalingDiagonal_of_boundaryKernel
    {a xi v : ι → R} {eigenvalue : R}
    (hv : BoundaryKernel v) :
    EigenRelation (rankOnePerturbation a xi) eigenvalue v ↔
      EigenRelation (scalingDiagonal a) eigenvalue v := by
  have hagree :
      rankOnePerturbation a xi v = scalingDiagonal a v :=
    rankOnePerturbation_agrees_on_boundary_kernel
      (a := a) (xi := xi) (v := v) (by simpa [BoundaryKernel] using hv)
  constructor
  · intro h
    simpa [EigenRelation, hagree] using h
  · intro h
    simpa [EigenRelation, hagree] using h

end CCMRankOne
end JensenLadder
