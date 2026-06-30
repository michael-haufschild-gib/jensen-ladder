import GaloisForLFunctions.EHKoszulDuality

/-!
# The superzeta as an additive resolvent trace (B23 verdict, Tier A)

This file machine-checks the structural core of the **B23 verdict**
(`docs/drafts/superzeta-tower-resolution-B23.md`): the Voros superzeta
`𝒵(w) = Σ_ρ ρ^{-w}` (whose integer values are the secular moments `P_k`) lives on
the **additive/spectral side of the seam**, as the *trace of resolvents* over the
zeros — structurally unlike a **multiplicative Euler product** over a prime base.
This is why, by the field's First Theorem (`EulerProduct.lean`), the superzeta has
no Euler product and the transcendence tower does not recurse spectrally.

For a finite multiset of (reciprocal-)zeros `r : Fin n → ℂ` (think `r i = ρ_i⁻¹`):

- `geom_eq_inv` : each per-zero geometric series `Σ_m rᵐ Xᵐ` is the inverse (the
  *resolvent*) `(1 − rX)⁻¹` in `ℂ⟦X⟧`.
- `superzeta_eq_sum_resolvent` : the superzeta generating function is the **sum**
  `Σ_i (1 − r_iX)⁻¹` — additive over the zeros (a trace), **not** a product.
- `superzeta_coeff_eq_powerSum` : its `k`-th coefficient is the power sum
  `Σ_i r_iᵏ` — the finite superzeta value `𝒵(k)` / secular moment `P_k`.

Contrast with `EHKoszulDuality.coeff_localFactor_series` / the Euler product, which
is a **product** `∏(1 − α x)` over a multiplicative base. The superzeta's additive
(`Σ`, spectral) versus the `L`-function's multiplicative (`∏`, prime) generating
structure is exactly the `[𝔾_a, 𝔾_m]` seam: this file is the finite, ledger-grade
witness that the superzeta sits on the spectral side, so it carries no Euler
product and no second difference-Galois `G_L`. It does **not** formalize the Voros
analytic continuation, the values-are-periods salvage, or the (conjectural)
off-line location of the superzeta's own zeros.
-/

open PowerSeries
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {n : ℕ}

/-- **The per-zero geometric series is the resolvent.** In `ℂ⟦X⟧`, the geometric
series `Σ_m rᵐ Xᵐ` is the inverse `(1 − rX)⁻¹` — the resolvent of the local
zero `r`. (The local factor `1 − rX` has constant coefficient `1 ≠ 0`, so it is a
unit; `geometric_localFactor_inv` exhibits the inverse.) -/
theorem geom_eq_inv (r : ℂ) : (mk fun m => r ^ m) = (1 - PowerSeries.C r * X)⁻¹ := by
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.C r * X) ≠ 0 := by simp
  rw [eq_comm, PowerSeries.inv_eq_iff_mul_eq_one hc, mul_comm]
  exact geometric_localFactor_inv r

/-- **The superzeta generating function is an additive resolvent trace.** For a
finite family of (reciprocal-)zeros `r`, the secular/superzeta generating function
`Σ_i Σ_m r_iᵐ Xᵐ` equals the **sum** of resolvents `Σ_i (1 − r_iX)⁻¹`. This is
additive over the zeros — a trace `Σ`, structurally **not** a product `∏`. It is
the finite witness that the superzeta lives on the additive/spectral side of the
`[𝔾_a, 𝔾_m]` seam, hence (B23, First Theorem) carries no Euler product. -/
theorem superzeta_eq_sum_resolvent (r : Fin n → ℂ) :
    (∑ i, (mk fun m => (r i) ^ m)) = ∑ i, (1 - PowerSeries.C (r i) * X)⁻¹ :=
  Finset.sum_congr rfl (fun i _ => geom_eq_inv (r i))

/-- **The superzeta value `𝒵(k)` is the secular power sum `P_k`.** The `k`-th
coefficient of the resolvent-trace generating function is the power sum
`Σ_i r_iᵏ` — i.e. the finite superzeta value `𝒵(k) = Σ_ρ ρ^{-k}` (with
`r_i = ρ_i⁻¹`), the secular moment `P_k`. These are the *values* the B23 salvage
places in the period corner. -/
theorem superzeta_coeff_eq_powerSum (r : Fin n → ℂ) (k : ℕ) :
    (PowerSeries.coeff k) (∑ i, (mk fun m => (r i) ^ m)) = ∑ i, (r i) ^ k := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => PowerSeries.coeff_mk k _)

end

end GaloisForLFunctions
