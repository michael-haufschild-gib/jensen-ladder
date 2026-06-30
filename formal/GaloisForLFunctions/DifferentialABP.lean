import Mathlib

/-!
# Differential ABP type obstruction: derivation versus Frobenius

This file formalizes the elementary algebraic floor behind
`docs/drafts/pipeline/2-fully-proven/multi-q-abp-criterion.md` and
`docs/drafts/pipeline/2-fully-proven/parametrized-differential-abp-escape.md`.

A Frobenius/ABP twist is multiplicative. A derivation is Leibniz. If one map is
both Leibniz and multiplicative, then it is the zero map. Thus a nonzero
derivation cannot itself be the multiplicative Frobenius twist needed by the
ABP values-to-functions lift.
-/

namespace GaloisForLFunctions

/-- Any Leibniz operator on a ring sends `1` to `0`. -/
theorem map_one_eq_zero_of_leibniz {R : Type*} [Ring R] (D : R → R)
    (hleibniz : ∀ x y, D (x * y) = D x * y + x * D y) : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by simpa using hleibniz 1 1
  have hcancel : (0 : R) = D 1 := by
    apply add_left_cancel (a := D 1)
    simpa using h
  exact hcancel.symm

/-- If a map kills `1` and is multiplicative, then it is the zero map. -/
theorem map_eq_zero_of_map_one_zero_of_map_mul {R : Type*} [MonoidWithZero R]
    (D : R → R) (h1 : D 1 = 0) (hmul : ∀ x y, D (x * y) = D x * D y) :
    ∀ x, D x = 0 := by
  intro x
  calc
    D x = D (x * 1) := congrArg D (mul_one x).symm
    _ = D x * D 1 := hmul x 1
    _ = D x * 0 := by rw [h1]
    _ = 0 := mul_zero (D x)

/-- A Leibniz operator that is also multiplicative is necessarily zero. -/
theorem map_eq_zero_of_leibniz_of_map_mul {R : Type*} [Ring R] (D : R → R)
    (hleibniz : ∀ x y, D (x * y) = D x * y + x * D y)
    (hmul : ∀ x y, D (x * y) = D x * D y) :
    ∀ x, D x = 0 :=
  map_eq_zero_of_map_one_zero_of_map_mul D (map_one_eq_zero_of_leibniz D hleibniz) hmul

/-- Equivalently, a nonzero Leibniz operator cannot be multiplicative. -/
theorem not_map_mul_of_leibniz_of_exists_ne_zero {R : Type*} [Ring R] (D : R → R)
    (hleibniz : ∀ x y, D (x * y) = D x * y + x * D y)
    (hne : ∃ x, D x ≠ 0) :
    ¬ ∀ x y, D (x * y) = D x * D y := by
  intro hmul
  rcases hne with ⟨x, hx⟩
  exact hx (map_eq_zero_of_leibniz_of_map_mul D hleibniz hmul x)

end GaloisForLFunctions
