import JensenLadder.HurwitzRealRootedLimit

/-!
# Functional-equation symmetry (evenness) of the entire `Ξ`

`HurwitzBridge.xiEntire z = ξ(½ + iz)` (pole-cancelled, entire) satisfies `xiEntire (-z) = xiEntire z`.
This is the Riemann functional equation `ξ(s) = ξ(1-s)` written in the variable `z` (with `s = ½ + iz`,
so `1 - s = ½ - iz = ½ + i(-z)`): the completed-zeta functional equation
`completedRiemannZeta₀_one_sub` supplies `Λ₀(1-s) = Λ₀(s)`, and the quadratic factor `s(s-1)` is
invariant under `s ↦ 1-s`.

Evenness is the structural foundation of the **squared variable** `w = z²` used by the carrier
canonical product (`CarrierCanonicalProduct`): an even entire function of `z` is a function of `z²`, which
is why `ξ(½+iz)` has order ½ / genus 0 in `w` and the carrier product carries no Hadamard prefactor.
RH-agnostic; Theorem M does not prove RH by itself.
-/

open Complex

namespace JensenLadder.HurwitzBridge

/-- **Functional-equation symmetry / evenness of `Ξ`:** `xiEntire (-z) = xiEntire z`. -/
lemma xiEntire_even (z : ℂ) : xiEntire (-z) = xiEntire z := by
  unfold xiEntire
  have hsub : (1/2 + I * (-z) : ℂ) = 1 - (1/2 + I * z) := by ring
  rw [hsub, completedRiemannZeta₀_one_sub]
  ring

/-- The zeros of `Ξ` are symmetric about `0`: `z` is a zero iff `-z` is. -/
lemma xiEntire_zero_neg_iff (z : ℂ) : xiEntire (-z) = 0 ↔ xiEntire z = 0 := by
  rw [xiEntire_even]

end JensenLadder.HurwitzBridge
