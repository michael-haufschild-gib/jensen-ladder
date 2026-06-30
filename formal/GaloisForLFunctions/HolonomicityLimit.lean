import Mathlib

/-!
# Holonomicity-limit nonclosure: stabilization anchor

This file formalizes the elementary integer-valued stabilization step from
`docs/drafts/pipeline/2-fully-proven/holonomicity-limit-nonclosure.md`.

The card's §2 corollary uses only this fact: a monotone bounded sequence of
natural-number coranks is eventually constant. The directed-sup corank identity,
G3 holonomicity implication, and comparison-functor statement are not formalized
here.
-/

namespace GaloisForLFunctions

private theorem monotoneNat_eventually_constant_of_bound_aux
    (c : ℕ → ℕ) (hmono : Monotone c) :
    ∀ B : ℕ, (∀ n, c n ≤ B) → ∃ N, ∀ n, N ≤ n → c n = c N := by
  intro B
  induction B with
  | zero =>
      intro hbound
      refine ⟨0, ?_⟩
      intro n _hn
      have hlen : c n ≤ 0 := hbound n
      have hle0 : c 0 ≤ 0 := hbound 0
      have hn0 : c n = 0 := by omega
      have h00 : c 0 = 0 := by omega
      rw [hn0, h00]
  | succ B ih =>
      intro hbound
      by_cases hhit : ∃ N, c N = B + 1
      · rcases hhit with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have hle : c n ≤ B + 1 := hbound n
        have hge : c N ≤ c n := hmono hn
        omega
      · have hbound' : ∀ n, c n ≤ B := by
          intro n
          have hle : c n ≤ B + 1 := hbound n
          have hne : c n ≠ B + 1 := by
            intro hcn
            exact hhit ⟨n, hcn⟩
          omega
        exact ih hbound'

/-- A monotone bounded natural-number sequence is eventually constant.

This is the formal integer-valued stabilization step used for the corank
sequence `c_T` in the holonomicity-limit card. -/
theorem monotoneNat_eventually_constant_of_bddAbove
    (c : ℕ → ℕ) (hmono : Monotone c) (hbdd : ∃ B, ∀ n, c n ≤ B) :
    ∃ N, ∀ n, N ≤ n → c n = c N := by
  rcases hbdd with ⟨B, hB⟩
  exact monotoneNat_eventually_constant_of_bound_aux c hmono B hB

end GaloisForLFunctions
