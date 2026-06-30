import Mathlib

/-!
# The finite DSS face: the spectrum's symmetric coordinates are algebraically independent

`carrier-unifies-dss-and-rh-faces.md` Brick 1, and `dss-multiplicity-estimate-spectral-genericity.md`.
The field's Object-X (the secular spectrum) has two faces on the single carrier germ `m_ξ`:

* the **RH face** — the carrier's global analytic type (Herglotz ⟺ `κ₋ = 0`); its finite layer is the
  exact Krein–Langer inertia `KreinLangerInertia.multiPair_carrier_exact_neg_inertia` (`κ₋ = #off-line
  zeros`), proved unconditionally;
* the **DSS face** — the algebraic genericity of the spectrum (the secular moments / symmetric
  functions are algebraically independent).

This file proves the **finite DSS face**: for `n` indeterminate spectral points, the elementary
symmetric functions `e_1, …, e_n` — equivalently the coefficients of the characteristic/secular
polynomial, the spectrum's natural coordinates — are algebraically independent over `ℚ`, so the
finite spectrum has full transcendence degree `n`. By Newton's identities (`MomentReconstruction`,
a `ℚ`-polynomial bijection in characteristic `0`) this is equivalent to algebraic independence of the
finite power-sum moments `P_1, …, P_n`.

This is the finite shadow of the DSS conjecture's genericity face — the analogue, on the DSS side, of
the finite exact-inertia result on the RH side. The **infinite** DSS apex (algebraic independence of
the full secular sequence `{P_k}`, reducing to `{π} ∪ {ζ(odd)} ∪ {Stieltjes γₙ}`) is open mathematics
and stays in the drafts. No infinite carrier `m_ξ`, no RH.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- **The finite DSS face: the spectrum's elementary-symmetric coordinates are algebraically
independent over `ℚ`.** For `n` indeterminate spectral points (variables of `MvPolynomial (Fin n) ℚ`),
the elementary symmetric functions `e_1, …, e_n` are algebraically independent — the secular spectrum
has full transcendence degree `n`. Proof: the fundamental theorem of symmetric polynomials
(`esymmAlgHom_injective`) says the algebra map `ℚ[Y_1,…,Y_n] → SymmetricSubalgebra`, `Y_i ↦ e_i`, is
injective; composing with the (injective) subalgebra inclusion identifies it with `aeval (e_·)`, whose
injectivity is exactly algebraic independence. By Newton's identities this transfers to the finite
power-sum moments `P_1, …, P_n` — the genuine finite shadow of the DSS conjecture. -/
theorem spectrum_esymm_algIndep (n : ℕ) :
    AlgebraicIndependent ℚ (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i + 1)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h : Function.Injective (MvPolynomial.esymmAlgHom (Fin n) ℚ n) :=
    MvPolynomial.esymmAlgHom_injective ℚ (by simp)
  have hval : (aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i + 1)) :
        MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ)
      = (Subalgebra.val _).comp (MvPolynomial.esymmAlgHom (Fin n) ℚ n) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.esymmAlgHom_apply]
  rw [hval, AlgHom.coe_comp]
  exact Subtype.val_injective.comp h

end

end GaloisForLFunctions
