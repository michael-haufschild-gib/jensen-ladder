import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import JensenLadder.FiniteEulerProductMixedLogGate

set_option autoImplicit false

/-!
# Von Mangoldt prime-power support as the additive Euler separator

The finite Euler-product gate (`FiniteEulerProductMixedLogGate`) records that
*multiplicativity* of a Dirichlet coefficient stream is the vanishing of the
mixed-log coefficient `a_{mn} - a_m * a_n`.  Its global/additive shadow is the
von Mangoldt function `Λ` (the coefficients of `-ζ'/ζ`): for a genuine Euler
product `Λ` is **supported on prime powers** — `Λ n = 0` unless `n` is a prime
power.

This file makes that prime-power support an explicit proved fact (drawn from
mathlib's `ArithmeticFunction.vonMangoldt`), pins `n = 6 = 2·3` — the smallest
modulus with two distinct prime factors — as the canonical *off-Euler* modulus
where `Λ` must vanish, and contrasts it with the Davenport–Heilbronn finite
pattern, whose mixed-log coefficient at `(2,3)` is `1 + κ² ≠ 0`.  Thus
**prime-power support of the log-derivative is the additive form of the Euler
separator, and DH-style nonmultiplicative replays fail it already at `n = 6`.**

This makes concrete the `vonMangoldtPrimePowerRow` interface that
`ChiralExplicitFormulaSource` currently carries only as the placeholder `True`.

This is **not** an RH proof and **not** a global domination theorem.  It is a
proved finite/arithmetic separator brick: it names the additive prime-power row
on which a single Euler product differs from a DH/Epstein/Beurling fake.
-/

namespace JensenLadder
namespace VonMangoldtPrimePowerSeparator

open ArithmeticFunction FiniteEulerProductMixedLogGate DHMultiplicityFakeGate

/-- **Prime-power support.** The von Mangoldt function vanishes off the prime
powers: if `n` is not a prime power then `Λ n = 0`.  This is the additive
(`log`-derivative) form of "a genuine Euler product has no cross-prime
coefficient." -/
theorem vonMangoldt_eq_zero_of_not_isPrimePow {n : ℕ} (h : ¬ IsPrimePow n) :
    vonMangoldt n = 0 :=
  vonMangoldt_eq_zero_iff.mpr h

/-- The smallest modulus with two distinct prime factors, `6 = 2 * 3`, is not a
prime power. -/
theorem not_isPrimePow_six : ¬ IsPrimePow (6 : ℕ) := by decide

/-- **Canonical off-Euler vanishing.** `Λ 6 = 0`: the additive form of the
multiplicativity relation `a_6 = a_2 * a_3` at the smallest cross-prime
modulus. -/
theorem vonMangoldt_six_eq_zero : vonMangoldt (6 : ℕ) = 0 :=
  vonMangoldt_eq_zero_of_not_isPrimePow not_isPrimePow_six

/-- A modulus carries genuine von Mangoldt (log-derivative) weight only if it is
a prime power: `Λ n ≠ 0 → IsPrimePow n`.  Equivalently, all the arithmetic
content of `-ζ'/ζ` lives on prime powers. -/
theorem isPrimePow_of_vonMangoldt_ne_zero {n : ℕ} (h : vonMangoldt n ≠ 0) :
    IsPrimePow n :=
  vonMangoldt_ne_zero_iff.mp h

/-!
## The separator: the Euler stream passes, the Davenport–Heilbronn pattern fails

For the genuine Euler stream the additive prime-power row holds at every
cross-prime modulus.  We record agreement at `n = 6` between the two forms:
the finite mixed-log coefficient of the unit (ζ) stream and the von Mangoldt
coefficient both vanish.  A DH-pattern stream instead has a *strictly positive*
mixed-log coefficient at `(2,3)`, i.e. nonzero log-derivative weight on the
non-prime-power `6` — it violates prime-power support.
-/

/-- For the unit (genuine Euler / ζ) coefficient stream, the finite mixed-log
coefficient at `(2,3)` vanishes, in agreement with `Λ 6 = 0`. -/
theorem zetaUnit_mixedLog23_agrees_vonMangoldt_six :
    mixedLogCoeffOf (fun _ : ℕ => (1 : ℝ)) 2 3 = 0
      ∧ vonMangoldt (6 : ℕ) = 0 :=
  ⟨zetaUnit_mixedLogCoeffOf_eq_zero 2 3, vonMangoldt_six_eq_zero⟩

/-- **Additive Euler separator.** Any Davenport–Heilbronn finite pattern places
*nonzero* log-derivative weight on the non-prime-power modulus `6` (its
mixed-log coefficient at `(2,3)` is `1 + κ² > 0`), while a genuine Euler product
has `Λ 6 = 0`.  Hence prime-power support of the log-derivative separates the
Euler product from DH-style nonmultiplicative replays at `n = 6`. -/
theorem dh_violates_primePower_support_at_six
    {a : ℕ -> ℝ} {kappa : ℝ} (h : DHPattern236 a kappa) :
    0 < mixedLogCoeffOf a 2 3 ∧ vonMangoldt (6 : ℕ) = 0 :=
  ⟨dhPattern236_mixedLogCoeffOf_pos h, vonMangoldt_six_eq_zero⟩

/-- The off-Euler modulus exhibiting the separation is `6`, a non-prime-power
that nonetheless carries DH log-derivative weight. -/
theorem dh_has_nonPrimePower_logWeight
    {a : ℕ -> ℝ} {kappa : ℝ} (h : DHPattern236 a kappa) :
    ¬ IsPrimePow (6 : ℕ) ∧ mixedLogCoeffOf a 2 3 ≠ 0 :=
  ⟨not_isPrimePow_six, dhPattern236_mixedLogCoeffOf_ne_zero h⟩

end VonMangoldtPrimePowerSeparator
end JensenLadder
