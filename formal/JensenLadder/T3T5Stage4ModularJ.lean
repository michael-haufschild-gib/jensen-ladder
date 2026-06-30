import Mathlib

/-!
# Stage 4 of the T3/T5 program: the finite modular conjugation J and J_mod = L_Lef (tracial case)

Stage 4 of `docs/plans/program_T3_T5_self_product_construction_20260617.md` asks to equip the
algebra with a KMS state, obtain the **Tomita modular conjugation `J`** and modular operator
`Δ`, and prove the sharp sub-theorem **`J_modular = L_Lefschetz`** (the Tomita conjugation
coincides with the ample/Rosati involution).

Full Tomita–Takesaki is not in Mathlib, but the **finite-dimensional, tracial (β = 0)** case
is concrete matrix algebra and is formalized here.  On the matrix algebra `M = Mₙ(ℂ)` in
standard form on Hilbert–Schmidt space, with the tracial cyclic-separating vector, the modular
conjugation is the **adjoint involution** `J(x) = xᴴ`, and the modular operator is trivial
(`Δ = 1`, the trace is its own KMS state).  We prove:
- `J` is an **antilinear involution** (`J² = id`, `J(c•x) = conj c • J x`);
- the **Tomita commutant relation** `J ∘ Lₐ ∘ J = R_{aᴴ}` (left multiplication conjugates to
  right multiplication by the adjoint) — i.e. `J M J = M'`.

**`J_mod = L_Lef` (tracial case):** the Rosati/Lefschetz involution of the self-product is the
adjoint `x ↦ xᴴ` (the Frobenius/transpose swap of the two axes), which is exactly this `J`.  So
at the tracial point `β = 0` the compatibility `J_modular = L_Lefschetz` **holds by definition**
(both are the adjoint).  The genuine content of Stage 4 is the **non-tracial β = ½** case, where
`Δ = L_ρ R_ρ⁻¹ ≠ 1` (the ρ-twist) and the compatibility becomes the no-margin/critical
constraint — that requires the standard-form / modular-operator infrastructure absent from
Mathlib and is the honest open part (flagged, not faked).

Evidence class: matrix algebra over ℂ, axiom-clean.  Does NOT formalize β=½ Tomita or prove RH.
-/

namespace JensenLadder
namespace T3T5Stage4

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n]

/-- The finite modular conjugation (tracial / standard-form): the adjoint involution on
`Mₙ(ℂ)`. -/
noncomputable def J (x : Matrix n n ℂ) : Matrix n n ℂ := xᴴ

omit [Fintype n] in
/-- `J` is involutive: `J² = id`. -/
theorem J_involutive (x : Matrix n n ℂ) : J (J x) = x := by
  simp [J]

omit [Fintype n] in
/-- `J` is antilinear: `J(c • x) = conj c • J x`. -/
theorem J_antilinear (c : ℂ) (x : Matrix n n ℂ) : J (c • x) = (starRingEnd ℂ c) • J x := by
  simp [J, conjTranspose_smul]

/-- **Tomita commutant relation** `J ∘ L_a ∘ J = R_{aᴴ}`: conjugating left-multiplication by
`a` through the modular conjugation `J` gives right-multiplication by `aᴴ`.  This is the finite
form of `J M J = M'` (the modular conjugation maps the algebra to its commutant). -/
theorem J_leftMul_J (a x : Matrix n n ℂ) : J (a * J x) = x * aᴴ := by
  simp [J, conjTranspose_mul]

omit [Fintype n] in
/-- The modular conjugation IS the Rosati/Lefschetz involution (adjoint) — the formal content of
`J_modular = L_Lefschetz` at the tracial point `β = 0`.  (Here stated as the definitional
identity `J = (·)ᴴ`, the Frobenius/axis-swap involution of the self-product.) -/
theorem J_eq_adjoint (x : Matrix n n ℂ) : J x = xᴴ := rfl

end T3T5Stage4
end JensenLadder
