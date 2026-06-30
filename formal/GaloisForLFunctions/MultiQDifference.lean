import GaloisForLFunctions.Core

/-!
# Local multi-q difference equation for Euler factors

This file formalizes the elementary identity from
`docs/drafts/infinite-base-difference-galois-for-L-functions.md` §18:
for the local Euler factor `f(x) = (1 - x)⁻¹`, dilation by `q` gives
`f(qx) = ((1 - x) / (1 - qx)) * f(x)`.

Lean's inverse is total, so the displayed meromorphic identity is stated on the
honest domain away from both poles, `x = 1` and `q * x = 1`. No Picard-Vessiot
or difference-Galois group is formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Multiplicative first-order relation for a dilated local Euler factor,
away from the two poles. -/
theorem localEulerFactor_dilation_relation {q x : ℂ}
    (hx : x ≠ 1) (hqx : q * x ≠ 1) :
    (1 - q * x) * localEulerFactor (q * x) =
      (1 - x) * localEulerFactor x := by
  rw [localEulerFactor_relation hqx, localEulerFactor_relation hx]

/-- The local Euler factor satisfies the first-order `q`-difference equation
`f(qx) = ((1 - x) / (1 - qx)) * f(x)` away from the poles. -/
theorem localEulerFactor_q_difference {q x : ℂ}
    (hx : x ≠ 1) (hqx : q * x ≠ 1) :
    localEulerFactor (q * x) =
      ((1 - x) / (1 - q * x)) * localEulerFactor x := by
  unfold localEulerFactor
  have hx0 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have hqx0 : 1 - q * x ≠ 0 := sub_ne_zero.mpr hqx.symm
  field_simp [hx0, hqx0]

/-- Prime-indexed dilation form: for `q_p = p⁻¹`, each Euler factor satisfies
its own first-order difference equation. -/
theorem localEulerFactor_prime_dilation_difference (p : Nat.Primes) {x : ℂ}
    (hx : x ≠ 1) (hpx : ((p : ℂ)⁻¹) * x ≠ 1) :
    localEulerFactor (((p : ℂ)⁻¹) * x) =
      ((1 - x) / (1 - ((p : ℂ)⁻¹) * x)) * localEulerFactor x := by
  exact localEulerFactor_q_difference (q := (p : ℂ)⁻¹) (x := x) hx hpx

end

end GaloisForLFunctions
