import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The modular-quotient obstruction (Rademacher lead cannot be a literal group quotient)

The "global winding / monodromy" lead for RH (object_x.md) is concretely realized
by the modular surface: closed modular geodesics are knots whose linking number
with the trefoil is the **Rademacher invariant** `Φ`, half the primitive of the
bounded Euler class of `PSL₂(ℤ)`.  A natural temptation is to obtain the
Euler-product winding as a *group quotient* `PSL₂(ℤ) ↠ ℚ^×_{>0}` of the modular
group onto the prime-multiplicative (Euler) group.

This is impossible, for a purely group-theoretic reason (object_x.md, "Confirmed
modular-quotient obstruction"):

* `PSL₂(ℤ) ≅ C₂ * C₃` (free product), whose abelianization is the **finite torsion**
  group `C₆ = ℤ/6`;
* the Euler group `ℚ^×_{>0} = ⊕_p ℤ` (free abelian on the primes) is **torsion-free**;
* any homomorphism to an abelian group factors through the abelianization, and a
  homomorphism from a torsion group to a torsion-free group is **trivial**.

Hence every homomorphism `PSL₂(ℤ) → ⊕_p ℤ` is trivial: the modular/Rademacher
lead cannot be a literal group quotient onto the Euler group.  It must instead be
a groupoid/span/boundary correspondence or a determinant-line pullback, whose
modular leg carries the bounded (Rademacher) class while a *separate* arithmetic
leg recovers the Euler product.

This module formalizes the load-bearing arithmetic core — *a homomorphism from a
torsion(-abelianization) group into a torsion-free group is trivial* — and
specializes it to `C₆ = ZMod 6` (the modular abelianization) mapping into `ℤ` (a
single prime exponent of the Euler group).  The presentation facts
`PSL₂(ℤ) ≅ C₂ * C₃` and `(PSL₂ℤ)^{ab} ≅ C₆` are the cited inputs (standard;
not re-proved here).

The useful residue is a no-go: the modular/Rademacher route cannot be a literal
group quotient onto the Euler group.
-/

namespace JensenLadder
namespace ModularQuotientNoGo

/-- `B` is (additively) torsion-free: a positive multiple of an element vanishes
only when the element vanishes.  The Euler group `⊕_p ℤ` has this property
(it is free abelian), as does each prime-exponent factor `ℤ`. -/
def TorsionFree (B : Type*) [AddMonoid B] : Prop :=
  ∀ (b : B) (n : ℕ), 0 < n → n • b = 0 → b = 0

/-- `ℤ` (a single prime exponent of the Euler group) is torsion-free. -/
theorem torsionFree_int : TorsionFree ℤ := by
  intro b n hn h
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (Nat.cast_eq_zero.mp h1) hn.ne'
  · exact h1

/-- **Torsion ⇒ trivial into torsion-free.**  If `a` is an `n`-torsion element
(`n • a = 0`, `n > 0`) and the target `B` is torsion-free, then every additive
homomorphism kills `a`. -/
theorem map_eq_zero_of_nsmul_eq_zero {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hB : TorsionFree B) {a : A} {n : ℕ} (hn : 0 < n)
    (ha : n • a = 0) : f a = 0 :=
  hB (f a) n hn (by rw [← map_nsmul, ha, map_zero])

/-- Every element of `C₆ = ZMod 6` is `6`-torsion. -/
theorem zmod6_six_nsmul (a : ZMod 6) : (6 : ℕ) • a = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **The modular abelianization admits only the trivial map to a torsion-free
group.**  Any additive homomorphism `C₆ = ZMod 6 → B` with `B` torsion-free is
identically zero. -/
theorem modular_ab_hom_to_torsionFree_trivial
    {B : Type*} [AddGroup B] (hB : TorsionFree B) (f : ZMod 6 →+ B) :
    ∀ a, f a = 0 :=
  fun a => map_eq_zero_of_nsmul_eq_zero f hB (by norm_num) (zmod6_six_nsmul a)

/-- The homomorphism is the zero homomorphism (extensional form). -/
theorem modular_ab_hom_to_torsionFree_eq_zero
    {B : Type*} [AddGroup B] (hB : TorsionFree B) (f : ZMod 6 →+ B) :
    f = 0 :=
  AddMonoidHom.ext (modular_ab_hom_to_torsionFree_trivial hB f)

/-- **Specialization to the Euler group's prime factor `ℤ`.**  Every additive
homomorphism `C₆ → ℤ` (modular abelianization → one prime exponent) is trivial.
Coordinatewise, every homomorphism `C₆ → ⊕_p ℤ` is trivial: the modular group has
no nontrivial map onto the Euler group. -/
theorem modular_ab_hom_to_int_trivial (f : ZMod 6 →+ ℤ) : ∀ a, f a = 0 :=
  modular_ab_hom_to_torsionFree_trivial torsionFree_int f

end ModularQuotientNoGo
end JensenLadder
