import Mathlib

/-!
# Self-dual reality of secular data (Tier A)

This file formalizes the reality skeleton underlying Sato–Tate / Ramanujan
(`automorphic-continent-rankin-selberg-ramanujan.md`): if a Satake (or zero)
multiset is **self-dual** — invariant under complex conjugation, the symmetry
`π ≅ π̄` — then every secular moment / Adams operation `Σ_{x∈s} x^m` is **real**
(fixed by conjugation).

This is the elementary conjugation bookkeeping that makes the secular data of a
self-dual automorphic representation real (so that the Sato–Tate measure and the
Hankel/moment matrices live over `ℝ`). It says nothing about equidistribution,
the Sato–Tate measure itself, or temperedness/Ramanujan as an analytic bound.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Self-dual reality (Sato–Tate / Ramanujan skeleton).** If a multiset `s` of
complex Satake parameters (or zeros) is invariant under complex conjugation
(self-duality `π ≅ π̄`), then every secular moment / Adams operation
`Σ_{x∈s} x^m` is fixed by conjugation, i.e. **real**. -/
theorem selfDual_moment_real (s : Multiset ℂ)
    (hs : s.map (starRingEnd ℂ) = s) (m : ℕ) :
    (starRingEnd ℂ) ((s.map (fun x => x ^ m)).sum)
      = (s.map (fun x => x ^ m)).sum := by
  rw [map_multiset_sum, Multiset.map_map]
  rw [show ((starRingEnd ℂ) ∘ fun x : ℂ => x ^ m)
        = ((fun x : ℂ => x ^ m) ∘ (starRingEnd ℂ)) from by
    funext x; simp [Function.comp_apply, map_pow]]
  rw [← Multiset.map_map (fun x : ℂ => x ^ m) (starRingEnd ℂ), hs]

end

end GaloisForLFunctions
