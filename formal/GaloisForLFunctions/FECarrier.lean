import GaloisForLFunctions.CarrierCauchy

/-!
# FE-doubling: a single off-line ζ-zero contributes negative inertia exactly 2

`carrier-unifies-dss-and-rh-faces.md` / `computations/carrier_real_zeros_inertia/`. The completed
`Ξ(z) = ξ(½+iz)` is even (`Ξ(−z)=Ξ(z)`) and real (`Ξ(z̄)=conj Ξ(z)`), so a single off-line zero `t₀`
(`Im t₀ > 0`) is forced into the **quadruple** `{t₀, t̄₀, −t₀, −t̄₀}` — two conjugate pairs with
`Im`-positive representatives `t₀` and `−t̄₀`. Hence the FE-faithful carrier has negative inertia
**exactly 2** per off-line zero, i.e. `κ₋ = 2·#{off-line zeros}` — a refinement of
`CarrierCauchy.multiPair_carrier_exact_neg_inertia` faithful to the functional equation, numerically
validated on the real ξ-zeros. Still finite — no infinite `m_ξ`, no RH.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions

noncomputable section

/-- **FE-doubling: a single off-line ζ-zero contributes κ₋ = 2.** An off-line zero `t₀` (`Im t₀ > 0`,
`Re t₀ ≠ 0`) is forced by the functional equation into the quadruple `{t₀, t̄₀, −t₀, −t̄₀}` = two
conjugate pairs (`Im`-positive representatives `t₀, −t̄₀`). So the FE-faithful carrier has negative
inertia **exactly 2** per off-line zero — `κ₋ = 2·#off-line zeros`. Instance of
`multiPair_carrier_exact_neg_inertia` at `k = 2` with poles `![t₀, −t̄₀]`. Numerically validated on the
real ξ-zeros (`computations/carrier_real_zeros_inertia/`). -/
theorem fe_quadruple_kappa_two (t₀ : ℂ) (z : Fin (2 + 2) → ℂ)
    (ht₀ : 0 < t₀.im) (hre : t₀.re ≠ 0) (hz : Function.Injective z)
    (htz : ∀ i j, (![t₀, -star t₀] i) ≠ z j)
    (hstz : ∀ i j, star (![t₀, -star t₀] i) ≠ z j)
    (w u : Fin 2 → (Fin (2 + 2) → ℂ))
    (hw : w = fun i j => (star (![t₀, -star t₀] i) - z j)⁻¹ + (![t₀, -star t₀] i - z j)⁻¹)
    (hu : u = fun i j => (star (![t₀, -star t₀] i) - z j)⁻¹ - (![t₀, -star t₀] i - z j)⁻¹) :
    (∀ W : Submodule ℂ (Fin (2 + 2) → ℂ),
        (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0)
        → Module.finrank ℂ W ≤ 2)
    ∧ (∃ W : Submodule ℂ (Fin (2 + 2) → ℂ), Module.finrank ℂ W = 2 ∧
        ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0) := by
  have hne : t₀ ≠ -star t₀ := by
    intro h; apply hre
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
    linarith
  have ht : ∀ i, 0 < ((![t₀, -star t₀]) i).im := by
    rw [Fin.forall_fin_two]
    refine ⟨by simpa using ht₀, ?_⟩
    have h1 : ((![t₀, -star t₀] : Fin 2 → ℂ) 1).im = t₀.im := by simp
    rw [h1]; exact ht₀
  have htinj : Function.Injective (![t₀, -star t₀]) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact multiPair_carrier_exact_neg_inertia ![t₀, -star t₀] z ht htinj hz htz hstz w u hw hu

end
end GaloisForLFunctions
