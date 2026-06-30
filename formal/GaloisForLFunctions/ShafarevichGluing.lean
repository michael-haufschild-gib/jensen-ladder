import Mathlib

/-!
# Multi-q Shafarevich gluing: rank-one diagonal kernel anchor

This file formalizes the semisimple diagonal algebra used in R1 of
`docs/drafts/pipeline/2-fully-proven/multi-q-shafarevich-gluing-group.md`.

In a joint eigenbasis, two commuting diagonal endomorphisms have
`ker(ST) = ker(S) + ker(T)`: coordinatewise, `s_i t_i x_i = 0` means each
coordinate belongs to the `S`-kernel part or the `T`-kernel part. This is the
linear algebra core behind the card's rank-one vanishing computation
`Ш_{p,q}^{(1)} = ker(τ_pτ_q)/(ker τ_p + ker τ_q) = 0`.

The nonabelian `H¹`, character-variety, and C5★ regularity layers are not
formalized here.
-/

namespace GaloisForLFunctions

/-- **Diagonal kernel splitting.** For diagonal scalar multipliers `a` and `b`,
membership in the kernel of the product multiplier is equivalent to a
coordinatewise decomposition into an `a`-kernel vector plus a `b`-kernel vector.

This is the eigenbasis form of `ker(ST)=ker(S)+ker(T)` used in the rank-one
Shafarevich-gluing vanishing argument. -/
theorem diagonalKer_mul_eq_sum_ker {ι K : Type*} [Field K]
    (a b x : ι → K) :
    (∀ i, a i * b i * x i = 0) ↔
      ∃ y z : ι → K,
        x = y + z ∧
        (∀ i, a i * y i = 0) ∧
        (∀ i, b i * z i = 0) := by
  classical
  constructor
  · intro h
    let y : ι → K := fun i => if a i = 0 then x i else 0
    let z : ι → K := fun i => if a i = 0 then 0 else x i
    refine ⟨y, z, ?_, ?_, ?_⟩
    · funext i
      by_cases ha : a i = 0
      · simp [y, z, ha]
      · simp [y, z, ha]
    · intro i
      by_cases ha : a i = 0
      · simp [y, ha]
      · simp [y, ha]
    · intro i
      by_cases ha : a i = 0
      · simp [z, ha]
      · have hbi : b i * x i = 0 := by
          have hi : a i * (b i * x i) = 0 := by
            rw [← mul_assoc]
            exact h i
          exact (mul_eq_zero.mp hi).resolve_left ha
        simp [z, ha, hbi]
  · rintro ⟨y, z, rfl, hy, hz⟩
    intro i
    calc
      a i * b i * ((y + z) i) = a i * b i * (y i + z i) := rfl
      _ = b i * (a i * y i) + a i * (b i * z i) := by ring
      _ = 0 := by rw [hy i, hz i]; ring

end GaloisForLFunctions
