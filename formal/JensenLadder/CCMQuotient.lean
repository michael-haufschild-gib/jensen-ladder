import JensenLadder.CCMRankOne

/-!
# Boundary quotient algebra for the finite CCM perturbation

The finite Connes--Consani--Moscovici rank-one operator kills the normalized
boundary direction and acts only on the quotient by that line.  This module
records that elementary algebra on finite functions:

* `BoundaryLine xi v` means `v` lies on the line spanned by `xi`;
* for normalized `xi`, `kernelPart xi` has kernel exactly that line;
* the rank-one perturbation is invariant under adding a boundary-line vector.

This is still only finite algebra.  It does not prove the CCM limiting
spectral identification, self-adjoint analytic convergence, or the Riemann
Hypothesis.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace CCMRankOne

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The line spanned by the boundary direction `xi`. -/
def BoundaryLine (xi v : ι → R) : Prop :=
  ∃ c : R, v = fun i => c * xi i

/-- Boundary functional on a pointwise scalar multiple. -/
theorem boundaryFunctional_smul
    (xi : ι → R) (c : R) :
    boundaryFunctional (fun i => c * xi i) = c * boundaryFunctional xi := by
  simp [boundaryFunctional, Finset.mul_sum]

/-- A boundary-line vector has zero boundary-kernel component when `xi` is
normalized. -/
theorem kernelPart_eq_zero_of_boundaryLine
    {xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi)
    (hv : BoundaryLine xi v) :
    kernelPart xi v = 0 := by
  rcases hv with ⟨c, rfl⟩
  have hboundary :
      boundaryFunctional (fun i => c * xi i) = c := by
    calc
      boundaryFunctional (fun i => c * xi i)
          = c * boundaryFunctional xi := boundaryFunctional_smul xi c
      _ = c * 1 := by rw [hxi]
      _ = c := by ring
  ext i
  simp [kernelPart, hboundary]

/-- If the boundary-kernel component of `v` is zero, then `v` lies on the
boundary line. -/
theorem boundaryLine_of_kernelPart_eq_zero
    {xi v : ι → R}
    (hv : kernelPart xi v = 0) :
    BoundaryLine xi v := by
  refine ⟨boundaryFunctional v, ?_⟩
  ext i
  have hpoint := congr_fun hv i
  dsimp [kernelPart] at hpoint
  exact sub_eq_zero.mp hpoint

/-- For a normalized boundary direction, `kernelPart xi` has kernel exactly the
boundary line spanned by `xi`. -/
theorem kernelPart_eq_zero_iff_boundaryLine
    {xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    kernelPart xi v = 0 ↔ BoundaryLine xi v := by
  constructor
  · exact boundaryLine_of_kernelPart_eq_zero
  · exact kernelPart_eq_zero_of_boundaryLine hxi

/-- Adding a multiple of the normalized boundary direction does not change the
boundary-kernel component. -/
theorem kernelPart_add_boundary_direction
    {xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi) (c : R) :
    kernelPart xi (fun i => v i + c * xi i) = kernelPart xi v := by
  have hboundary :
      boundaryFunctional (fun i => v i + c * xi i) =
        boundaryFunctional v + c := by
    calc
      boundaryFunctional (fun i => v i + c * xi i)
          = boundaryFunctional v + boundaryFunctional (fun i => c * xi i) := by
              simp [boundaryFunctional, Finset.sum_add_distrib]
      _ = boundaryFunctional v + c * boundaryFunctional xi := by
              rw [boundaryFunctional_smul]
      _ = boundaryFunctional v + c * 1 := by rw [hxi]
      _ = boundaryFunctional v + c := by ring
  ext i
  simp [kernelPart, hboundary]
  ring

/-- Two vectors represent the same boundary-quotient class when they differ by
a vector on the boundary line. -/
def SameBoundaryClass (xi v w : ι → R) : Prop :=
  ∃ c : R, v = fun i => w i + c * xi i

/-- Same-boundary-class is reflexive. -/
theorem sameBoundaryClass_refl
    (xi v : ι → R) :
    SameBoundaryClass xi v v := by
  refine ⟨0, ?_⟩
  ext i
  simp

/-- Same-boundary-class is symmetric. -/
theorem sameBoundaryClass_symm
    {xi v w : ι → R}
    (hvw : SameBoundaryClass xi v w) :
    SameBoundaryClass xi w v := by
  rcases hvw with ⟨c, hvw⟩
  refine ⟨-c, ?_⟩
  ext i
  have hpoint := congr_fun hvw i
  rw [hpoint]
  ring

/-- Same-boundary-class is transitive. -/
theorem sameBoundaryClass_trans
    {xi u v w : ι → R}
    (huv : SameBoundaryClass xi u v)
    (hvw : SameBoundaryClass xi v w) :
    SameBoundaryClass xi u w := by
  rcases huv with ⟨c, huv⟩
  rcases hvw with ⟨d, hvw⟩
  refine ⟨d + c, ?_⟩
  ext i
  have huv_i := congr_fun huv i
  have hvw_i := congr_fun hvw i
  rw [huv_i, hvw_i]
  ring

/-- Boundary-line membership is the same as being boundary-equivalent to zero. -/
theorem sameBoundaryClass_zero_iff_boundaryLine
    {xi v : ι → R} :
    SameBoundaryClass xi v 0 ↔ BoundaryLine xi v := by
  constructor
  · rintro ⟨c, hv⟩
    refine ⟨c, ?_⟩
    simpa using hv
  · rintro ⟨c, hv⟩
    refine ⟨c, ?_⟩
    simpa using hv

/-- Normalized `kernelPart` is constant on boundary-quotient classes. -/
theorem kernelPart_eq_of_sameBoundaryClass
    {xi v w : ι → R}
    (hxi : NormalizedBoundaryVector xi)
    (hvw : SameBoundaryClass xi v w) :
    kernelPart xi v = kernelPart xi w := by
  rcases hvw with ⟨c, rfl⟩
  exact kernelPart_add_boundary_direction (xi := xi) (v := w) hxi c

/-- For normalized `xi`, equality of boundary-kernel components is exactly
equality in the boundary quotient. -/
theorem kernelPart_eq_iff_sameBoundaryClass
    {xi v w : ι → R}
    (hxi : NormalizedBoundaryVector xi) :
    kernelPart xi v = kernelPart xi w ↔ SameBoundaryClass xi v w := by
  constructor
  · intro hkernel
    refine ⟨boundaryFunctional v - boundaryFunctional w, ?_⟩
    ext i
    have hpoint := congr_fun hkernel i
    dsimp [kernelPart] at hpoint
    calc
      v i = (v i - boundaryFunctional v * xi i) +
          boundaryFunctional v * xi i := by ring
      _ = (w i - boundaryFunctional w * xi i) +
          boundaryFunctional v * xi i := by rw [hpoint]
      _ = w i + (boundaryFunctional v - boundaryFunctional w) * xi i := by ring
  · exact kernelPart_eq_of_sameBoundaryClass hxi

/-- The rank-one perturbation depends only on the boundary-kernel component. -/
theorem rankOnePerturbation_eq_of_kernelPart_eq
    {a xi v w : ι → R}
    (hvw : kernelPart xi v = kernelPart xi w) :
    rankOnePerturbation a xi v = rankOnePerturbation a xi w := by
  rw [rankOnePerturbation_eq_scalingDiagonal_kernelPart,
    rankOnePerturbation_eq_scalingDiagonal_kernelPart, hvw]

/-- The rank-one perturbation is constant on normalized boundary-quotient
classes. -/
theorem rankOnePerturbation_eq_of_sameBoundaryClass
    {a xi v w : ι → R}
    (hxi : NormalizedBoundaryVector xi)
    (hvw : SameBoundaryClass xi v w) :
    rankOnePerturbation a xi v = rankOnePerturbation a xi w :=
  rankOnePerturbation_eq_of_kernelPart_eq
    (a := a) (xi := xi)
    (kernelPart_eq_of_sameBoundaryClass hxi hvw)

/-- The rank-one perturbation is invariant under adding a multiple of the
normalized killed direction. -/
theorem rankOnePerturbation_add_boundary_direction
    {a xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi) (c : R) :
    rankOnePerturbation a xi (fun i => v i + c * xi i) =
      rankOnePerturbation a xi v :=
  rankOnePerturbation_eq_of_kernelPart_eq
    (a := a) (xi := xi) (v := fun i => v i + c * xi i) (w := v)
    (kernelPart_add_boundary_direction (xi := xi) (v := v) hxi c)

/-- The rank-one perturbation kills every vector on the normalized boundary
line. -/
theorem rankOnePerturbation_eq_zero_of_boundaryLine
    {a xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi)
    (hv : BoundaryLine xi v) :
    rankOnePerturbation a xi v = 0 := by
  rw [rankOnePerturbation_eq_scalingDiagonal_kernelPart]
  rw [kernelPart_eq_zero_of_boundaryLine hxi hv]
  ext i
  simp [scalingDiagonal]

/-- For normalized `xi`, zero boundary-kernel component is equivalent to the
zero eigen-relation of the rank-one perturbation on the killed boundary line. -/
theorem boundaryLine_zero_eigenRelation
    {a xi v : ι → R}
    (hxi : NormalizedBoundaryVector xi)
    (hv : BoundaryLine xi v) :
    EigenRelation (rankOnePerturbation a xi) 0 v := by
  dsimp [EigenRelation]
  rw [rankOnePerturbation_eq_zero_of_boundaryLine hxi hv]
  ext i
  simp

end CCMRankOne
end JensenLadder
