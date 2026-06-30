import GaloisForLFunctions.Core

/-!
# The Arakelov `w`-coordinate: FE as inversion, critical line as the unit circle (Tier A)

Formalizes the elementary core of `computations/arakelov_w_coordinate/` and
`docs/drafts/arakelov-height-of-zeros.md` §1–2: in the coordinate `w_ρ = 1 - 1/ρ = (ρ-1)/ρ`,

* the functional equation `σ : ρ ↦ 1 - ρ` acts as **inversion** `w_ρ · w_{1-ρ} = 1`;
* the critical line is the **unit circle** `‖w_ρ‖ = 1 ⟺ Re ρ = 1/2`.

This is the multiplicative-coordinate companion of `SigmaOrbit.lean` (the additive `σ∘conj`
fixed-locus form). Elementary complex arithmetic; no zero, no RH, no height inequality is
formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

open Complex

/-- The Arakelov `w`-coordinate of a point `ρ`: `w_ρ = 1 - 1/ρ`. -/
def arakelovW (ρ : ℂ) : ℂ := 1 - ρ⁻¹

theorem arakelovW_eq_div (ρ : ℂ) (h0 : ρ ≠ 0) : arakelovW ρ = (ρ - 1) / ρ := by
  rw [arakelovW]; field_simp

/-- **FE as inversion.** The functional-equation partner satisfies `w_ρ · w_{1-ρ} = 1`
(for `ρ ∉ {0, 1}`). -/
theorem arakelovW_mul_sigma (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    arakelovW ρ * arakelovW (sigma ρ) = 1 := by
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [arakelovW, arakelovW, sigma]
  field_simp
  ring

/-- **Critical line = unit circle in the `w`-coordinate.** `‖w_ρ‖ = 1 ⟺ Re ρ = 1/2`. -/
theorem arakelovW_norm_one_iff_critical (ρ : ℂ) (h0 : ρ ≠ 0) :
    ‖arakelovW ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hbridge : ‖arakelovW ρ‖ = 1 ↔ Complex.normSq (arakelovW ρ) = 1 := by
    rw [← Complex.sq_norm]
    constructor
    · intro h; rw [h]; norm_num
    · intro h; nlinarith [norm_nonneg (arakelovW ρ)]
  rw [hbridge, arakelovW_eq_div ρ h0, map_div₀,
      div_eq_one_iff_eq (Complex.normSq_pos.mpr h0).ne']
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith [h]

/-- **Cayley inside/outside dichotomy.** `‖w_ρ‖ < 1 ⟺ Re ρ > 1/2`: the Arakelov map sends the open
right half-plane to the open unit disk (and `Re ρ < 1/2` to its exterior). With
`arakelovW_norm_one_iff_critical` this is the Cayley transform intertwining the line-self-adjoint
(real spectrum) and circle-unitary (spectrum on `|w|=1`) operator pictures. -/
theorem arakelovW_norm_lt_one_iff (ρ : ℂ) (h0 : ρ ≠ 0) :
    ‖arakelovW ρ‖ < 1 ↔ 1 / 2 < ρ.re := by
  have hbridge : ‖arakelovW ρ‖ < 1 ↔ Complex.normSq (arakelovW ρ) < 1 := by
    rw [← Complex.sq_norm]
    constructor
    · intro h; nlinarith [norm_nonneg (arakelovW ρ)]
    · intro h; nlinarith [norm_nonneg (arakelovW ρ)]
  rw [hbridge, arakelovW_eq_div ρ h0, map_div₀, div_lt_one (Complex.normSq_pos.mpr h0)]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith [h]

/-- The Arakelov map `ρ ↦ 1 - 1/ρ` is **injective** — an honest Möbius/Cayley change of coordinate.
Together with `arakelovW_norm_one_iff_critical` and `arakelovW_norm_lt_one_iff` it is the bijection
sending the critical line to the unit circle and the right half-plane to the open disk: the rigorous
intertwiner between the line (self-adjoint) and circle (unitary) operator pictures. -/
theorem arakelovW_injective {ρ ρ' : ℂ} (e : arakelovW ρ = arakelovW ρ') : ρ = ρ' := by
  have h : ρ⁻¹ = ρ'⁻¹ := by
    rw [arakelovW, arakelovW] at e
    linear_combination -e
  exact inv_inj.mp h

end

end GaloisForLFunctions
