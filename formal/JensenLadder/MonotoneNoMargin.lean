/-
# The monotone no-margin lemma (RH-free, axiom-clean)

Author: berry, 2026-06-18. Program: `program_T3_T5_self_product_construction`.

This file formalizes the abstract structural content behind the "monotone no-margin" observation for the
finite CCM Weil form `H_N` (even sector, genuine weight).

## Mathematical background (the application)
The even-sector Weil form `H_N` has **N-independent entries** (the grid `d_n = 2πn/L`, `L=2logλ`, and the Weil
kernel do not depend on the truncation `N`; only the matrix *size* grows). This was verified exactly off-line
(`scripts/.../berry_compression_check_20260618.txt`: `max|H_8[i,j]−H_12[i,j]| = 0`). Hence `H_N` is the
principal **compression** of `H_{N+1}` on a **nested** basis, so its bottom eigenvalue equals the infimum of the
Rayleigh quotient over the increasing subspaces `V_N ⊆ V_{N+1}`. The bottom eigenvalue is therefore
**antitone in `N`** (the variational form of Cauchy interlacing for the smallest eigenvalue).

## What is proved here (abstract, reusable)
Modelling "the bottom of the form on level `N`" as `beta N := sInf (Q '' S N)` for a fixed real-valued `Q` and
a nested family of nonempty, bounded-below level sets `S`, we prove:
* `beta_antitone`   — `beta` is antitone (inf over a larger set is smaller);
* `nonneg_iInf_iff` — positivity at every level ⟺ the infimum of the levels is `≥ 0`
                       (the "RH ⟺ a single monotone-limit condition" restatement);
* `permanent_witness`— a single level with negative bottom forces every later level negative
                       (the "¬RH ⟺ a permanent finite witness" restatement).

These are RH-free order facts. They do **not** prove positivity (`0 ≤ ⨅ beta` = Weil positivity = RH); they
reshape it from an infinite family of inequalities into one monotone-limit condition with a clean falsification
criterion. The concrete instantiation (`Q` = the even-sector Weil Rayleigh quotient, `S N` = the unit sphere of
the level-`N` subspace) is supplied by the verified `H_N`-compression structure above.
-/
import Mathlib

open Set

namespace MonotoneNoMargin

variable {V : Type*} (Q : V → ℝ) (S : ℕ → Set V)

/-- Bottom of the form on level `N`: the infimum of `Q` over the level-`N` set. -/
noncomputable def beta (N : ℕ) : ℝ := sInf (Q '' S N)

/-- Abstract Cauchy-interlacing / min-over-nested-subspaces fact: if the levels are nested
(`Monotone S`), nonempty, and `Q` is bounded below on each level, the bottoms are **antitone**. -/
theorem beta_antitone (hS : Monotone S) (hne : ∀ N, (S N).Nonempty)
    (hbdd : ∀ N, BddBelow (Q '' S N)) : Antitone (beta Q S) := by
  intro m n hmn
  exact csInf_le_csInf (hbdd n) ((hne m).image Q) (image_mono (hS hmn))

/-- RH-as-a-single-limit: nonnegativity at every level ⟺ the infimum of the bottoms is `≥ 0`. -/
theorem nonneg_iInf_iff (hbdd : BddBelow (range (beta Q S))) :
    0 ≤ ⨅ N, beta Q S N ↔ ∀ N, 0 ≤ beta Q S N :=
  le_ciInf_iff hbdd

/-- Permanent finite witness: one level with negative bottom forces all later levels negative. -/
theorem permanent_witness (hanti : Antitone (beta Q S)) {N₀ : ℕ}
    (h : beta Q S N₀ < 0) : ∀ N, N₀ ≤ N → beta Q S N < 0 :=
  fun _ hN => lt_of_le_of_lt (hanti hN) h

end MonotoneNoMargin
