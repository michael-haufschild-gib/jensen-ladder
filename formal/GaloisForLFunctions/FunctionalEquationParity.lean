import Mathlib

/-!
# Functional-equation parity of secular moments (Tier A)

This file formalizes the **σ-parity skeleton** of the field:
`hypertranscendental_galois_field_foundations.md` §22 (centered odd moments
`τ_{2m+1}=0`) and `difference-galois-cohomology.md` §3 (the cohomological
grading `σ|_{∧ᵏV}=(−1)ᵏ` is the functional-equation parity).

The functional equation makes the zero multiset invariant under the reflection
`ρ ↦ 1−ρ`; centered at the critical line this is invariance under negation
`x ↦ −x`. The content here is the elementary consequence: for any multiset of
complex numbers invariant under negation, **every odd power sum vanishes**
(`Σ x^{2m+1} = 0`), while even power sums survive. This is the FE moment-parity
`τ_{2m+1}=0` of §22, at ledger grade.

This is purely the parity bookkeeping for a negation-symmetric multiset. It says
nothing about which zeros are actually symmetric (the functional equation itself),
about the exterior-algebra cup product, or about RH.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **FE/σ-parity (foundations §22).** If a multiset `s` of complex numbers is
invariant under negation `x ↦ −x` (the functional-equation symmetry centered at
the critical line), then every **odd** power sum vanishes:
`Σ_{x∈s} x^{2m+1} = 0`. Proof: the odd-power image is again negation-invariant,
so its sum equals its own negation, hence is `0` in characteristic zero. -/
theorem fe_odd_moment_vanish (s : Multiset ℂ)
    (hs : s.map (fun x => -x) = s) (m : ℕ) :
    (s.map (fun x => x ^ (2 * m + 1))).sum = 0 := by
  have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
  set T := s.map (fun x => x ^ (2 * m + 1)) with hT
  -- the odd-power image `T` is itself negation-invariant
  have hTneg : T.map (fun y => -y) = T := by
    rw [hT, Multiset.map_map]
    have hcomp : ((fun y => -y) ∘ (fun x : ℂ => x ^ (2 * m + 1)))
        = ((fun x : ℂ => x ^ (2 * m + 1)) ∘ (fun x => -x)) := by
      funext x
      simp only [Function.comp_apply, hodd.neg_pow]
    rw [hcomp, ← Multiset.map_map, hs]
  -- hence `T.sum = -T.sum`, so `T.sum = 0` in characteristic zero
  have hself : T.sum = -T.sum := by
    conv_lhs => rw [← hTneg]
    exact Multiset.sum_map_neg' T
  have hadd : T.sum + T.sum = 0 := by
    nth_rewrite 1 [hself]; ring
  exact add_self_eq_zero.mp hadd

/-- **FE σ-parity, centered at the critical line (the literal functional
equation).** If a zero multiset `s` is invariant under the functional-equation
reflection `ρ ↦ 1 − ρ`, then every **centered odd moment** vanishes:
`Σ_{ρ∈s} (ρ − ½)^{2m+1} = 0`. This is foundations §22 (`τ_{2m+1}=0`) for the
actual functional equation: the shifted multiset `{ρ − ½}` is negation-invariant,
so `fe_odd_moment_vanish` applies. -/
theorem fe_centered_odd_moment_vanish (s : Multiset ℂ)
    (hs : s.map (fun x => 1 - x) = s) (m : ℕ) :
    (s.map (fun x => (x - 1 / 2) ^ (2 * m + 1))).sum = 0 := by
  have ht : (s.map (fun x => x - 1 / 2)).map (fun y => -y)
      = s.map (fun x => x - 1 / 2) := by
    rw [Multiset.map_map]
    have h1 : ((fun y => -y) ∘ (fun x : ℂ => x - 1 / 2)) = (fun x : ℂ => 1 / 2 - x) := by
      funext x; simp only [Function.comp_apply]; ring
    rw [h1]
    nth_rewrite 2 [← hs]
    rw [Multiset.map_map]
    congr 1
    funext x; simp only [Function.comp_apply]; ring
  have key := fe_odd_moment_vanish (s.map (fun x => x - 1 / 2)) ht m
  rwa [Multiset.map_map] at key

end

end GaloisForLFunctions
