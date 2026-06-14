import Mathlib.Tactic

/-!
# det_reg post-hoc normalization no-go

This module formalizes a small scalar obstruction in the determinant-to-`Xi`
route.

If each finite determinant may be rescaled after seeing the target basepoint
value, then exact basepoint agreement is automatic whenever the original
basepoint value is nonzero.  If the target basepoint value is also nonzero, that
rescaling preserves the zero set, so it preserves any finite real-zero row.

Therefore basepoint normalization is load-bearing only when the scalar is
predeclared by the determinant normalization and trace package.  A post-hoc
scalar fit is not det_reg -> Xi evidence.

Evidence class: proved finite algebra lemma.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace DeterminantNormalizationNoGo

/-- A family has only real zeros if every zero of every member has zero
imaginary part. -/
def AllZerosRealFamily {ι : Type*} (F : ι -> ℂ -> ℂ) : Prop :=
  ∀ a : ι, ∀ z : ℂ, F a z = 0 -> z.im = 0

/-- The post-hoc scalar that forces basepoint agreement with a target. -/
noncomputable def posthocScale {ι : Type*} (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ)
    (w₀ : ℂ) (a : ι) : ℂ :=
  T w₀ / F a w₀

/-- The post-hoc normalized family. -/
noncomputable def posthocNormalized {ι : Type*} (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ)
    (w₀ : ℂ) (a : ι) (z : ℂ) : ℂ :=
  posthocScale F T w₀ a * F a z

/--
Post-hoc normalization forces exact basepoint agreement whenever the original
basepoint value is nonzero.
-/
theorem posthocNormalized_basepoint_eq {ι : Type*}
    (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ) (w₀ : ℂ) (a : ι)
    (hF : F a w₀ ≠ 0) :
    posthocNormalized F T w₀ a w₀ = T w₀ := by
  unfold posthocNormalized posthocScale
  field_simp [hF]

/-- If both target and original basepoint values are nonzero, the post-hoc
scalar is nonzero. -/
theorem posthocScale_ne_zero {ι : Type*}
    (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ) (w₀ : ℂ) (a : ι)
    (hT : T w₀ ≠ 0)
    (hF : F a w₀ ≠ 0) :
    posthocScale F T w₀ a ≠ 0 := by
  unfold posthocScale
  exact div_ne_zero hT hF

/-- Multiplication by a nonzero scalar preserves the zero set of one family
member. -/
theorem scalar_mul_eq_zero_iff {ι : Type*}
    (F : ι -> ℂ -> ℂ) (c : ι -> ℂ) (a : ι) (z : ℂ)
    (hc : c a ≠ 0) :
    c a * F a z = 0 ↔ F a z = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    simp [h]

/-- Nonzero scalar normalization preserves the finite real-zero row. -/
theorem allZerosRealFamily_scalar_mul_iff {ι : Type*}
    (F : ι -> ℂ -> ℂ) (c : ι -> ℂ)
    (hc : ∀ a : ι, c a ≠ 0) :
    AllZerosRealFamily (fun a z => c a * F a z) ↔ AllZerosRealFamily F := by
  constructor
  · intro h a z hz
    exact h a z (by simp [hz])
  · intro h a z hz
    exact h a z ((scalar_mul_eq_zero_iff F c a z (hc a)).1 hz)

/-- Post-hoc normalization preserves the real-zero row when the target and
basepoint values are nonzero. -/
theorem allZerosRealFamily_posthocNormalized_iff {ι : Type*}
    (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ) (w₀ : ℂ)
    (hT : T w₀ ≠ 0)
    (hF : ∀ a : ι, F a w₀ ≠ 0) :
    AllZerosRealFamily (posthocNormalized F T w₀) ↔ AllZerosRealFamily F := by
  unfold posthocNormalized
  exact allZerosRealFamily_scalar_mul_iff F (posthocScale F T w₀)
    (fun a => posthocScale_ne_zero F T w₀ a hT (hF a))

/-- A post-hoc scalar family always exists that forces basepoint agreement. -/
theorem exists_posthoc_scalar_basepoint_match {ι : Type*}
    (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ) (w₀ : ℂ)
    (hF : ∀ a : ι, F a w₀ ≠ 0) :
    ∃ c : ι -> ℂ, ∀ a : ι, c a * F a w₀ = T w₀ := by
  refine ⟨posthocScale F T w₀, ?_⟩
  intro a
  exact posthocNormalized_basepoint_eq F T w₀ a (hF a)

/--
If the target basepoint value is also nonzero, the matching post-hoc scalar can
be chosen nonzero and zero-set-preserving.
-/
theorem exists_nonzero_posthoc_scalar_basepoint_match_and_zero_preserving
    {ι : Type*}
    (F : ι -> ℂ -> ℂ) (T : ℂ -> ℂ) (w₀ : ℂ)
    (hT : T w₀ ≠ 0)
    (hF : ∀ a : ι, F a w₀ ≠ 0) :
    ∃ c : ι -> ℂ,
      (∀ a : ι, c a * F a w₀ = T w₀) ∧
      (∀ a : ι, c a ≠ 0) ∧
      (∀ a : ι, ∀ z : ℂ, c a * F a z = 0 ↔ F a z = 0) := by
  refine ⟨posthocScale F T w₀, ?_, ?_, ?_⟩
  · intro a
    exact posthocNormalized_basepoint_eq F T w₀ a (hF a)
  · intro a
    exact posthocScale_ne_zero F T w₀ a hT (hF a)
  · intro a z
    exact scalar_mul_eq_zero_iff F (posthocScale F T w₀) a z
      (posthocScale_ne_zero F T w₀ a hT (hF a))

end DeterminantNormalizationNoGo
end JensenLadder

