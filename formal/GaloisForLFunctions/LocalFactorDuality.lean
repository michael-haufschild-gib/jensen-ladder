import Mathlib

/-!
# Functional-equation self-duality of the local L-factor (Tier A)

This file formalizes the Euler-factor-level functional equation of branch B30 /
the automorphic continent (`automorphic-continent-rankin-selberg-ramanujan.md`):
if a Satake multiset is **self-dual** (`π ≅ π̃`, i.e. the parameters are closed
under inversion `α ↦ α⁻¹`), then the local L-factor `∏_i (1 − α_i x)` is
invariant under `α ↦ α⁻¹`.

This is the multiset relabelling underlying the local functional equation. It
does not formalize the global functional equation, the archimedean factor, or
the Rankin–Selberg theory.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Local L-factor self-duality (FE at the Euler-factor level).** If the Satake
multiset `s` is inversion-closed (`{α_i} = {α_i⁻¹}`, the self-duality `π ≅ π̃`),
then the local L-factor `∏_i (1 − α_i x)` equals `∏_i (1 − α_i⁻¹ x)`. -/
theorem selfDual_localFactor_eq (s : Multiset ℂ)
    (hs : s.map (fun a => a⁻¹) = s) (x : ℂ) :
    (s.map (fun a => 1 - a * x)).prod = (s.map (fun a => 1 - a⁻¹ * x)).prod := by
  nth_rewrite 1 [← hs]
  rw [Multiset.map_map]
  rfl

end

end GaloisForLFunctions
