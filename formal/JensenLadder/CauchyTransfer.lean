import Mathlib.Analysis.Complex.Liouville

/-!
# Deterministic Cauchy-transfer core

This file packages the SD-C5 consumer step.  Once a holomorphic log-error
function is bounded by `eta` on the boundary of a `k`-disk of radius `rho`,
Cauchy's estimate gives the derivative/cumulant error bound
`j! * eta / rho^j`.
-/

namespace JensenLadder
namespace CauchyTransfer

open Metric

/--
SD-C5 Cauchy-transfer endpoint.

For a complex log-error function `F` on the `k`-disk, a boundary bound
`‖F z‖ <= eta` transfers to the `j`-th derivative bound at the center.
In the SD-C application, `F = log M_cert - log M_true` and
`eta = -log(1 - tau / mu)`.
-/
theorem iteratedDeriv_norm_le_of_boundary_norm_le
    {center : ℂ} {rho eta : ℝ} {F : ℂ → ℂ} (j : ℕ)
    (hrho : 0 < rho)
    (hF : DiffContOnCl ℂ F (ball center rho))
    (heta : ∀ z ∈ sphere center rho, ‖F z‖ ≤ eta) :
    ‖iteratedDeriv j F center‖ ≤ j.factorial * eta / rho ^ j := by
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hrho hF heta

/--
First-derivative specialization of SD-C5.
-/
theorem deriv_norm_le_of_boundary_norm_le
    {center : ℂ} {rho eta : ℝ} {F : ℂ → ℂ}
    (hrho : 0 < rho)
    (hF : DiffContOnCl ℂ F (ball center rho))
    (heta : ∀ z ∈ sphere center rho, ‖F z‖ ≤ eta) :
    ‖deriv F center‖ ≤ eta / rho := by
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrho hF heta

end CauchyTransfer
end JensenLadder
