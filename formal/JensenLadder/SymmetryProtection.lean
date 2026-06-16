import Mathlib

/-!
# Symmetry protection of the no-margin wall (RH-agnostic)

The functional equation `ρ ↦ 1 - ρ` and reality `ρ ↦ conj ρ` of the completed zeta
function force an off-line zero into a **quartet** `1/2 ± β ± iγ`.  Recentering (subtract
`1/2`) and writing `a := β` (the off-line displacement) and `b := iγ`, the four recentered
points are `± a ± b`.

The `k`-th power-sum moment of this quartet,
`moment a b k = (a+b)^k + (a-b)^k + (-a+b)^k + (-a-b)^k`,
is the data that every analytic (Weil / Hankel / Jensen) positivity functional is built
from (these are functions of the secondary-zeta power sums `Σ (ρ-1/2)^k`).

We prove the **symmetry protection**:

* `moment_even`   : the quartet moment is EVEN in the off-line displacement `a`
  (invariant under `a ↦ -a`, the functional-equation involution in recentered coordinates).
  An even function has no first-order term, so the *first variation* of the moment in the
  off-line displacement vanishes.
* `moment_even_b` : it is also even in `b` (the reality/`γ` involution).
* `moment_odd_eq_zero` : the odd-degree moments vanish identically.

Consequence (mathematical, recorded here as documentation, not a Lean statement):
any functional that is a function of the moments has vanishing first-order variation in the
off-line displacement.  Hence the no-margin wall is a **symmetry-protected second-order
degeneracy**: soft-margin / first-order positivity methods cannot detect an off-line zero,
and the discriminating content sits in the (indefinite) second variation.

This module is RH-agnostic structural algebra.  It does **not** prove the Riemann
Hypothesis; Theorem M does not prove RH by itself.  It rigorously explains why a whole
class of (first-order / soft-margin positivity) methods cannot work.
-/

namespace JensenLadder.SymmetryProtection

variable {R : Type*} [CommRing R]

/-- `k`-th power-sum moment of the recentered off-line quartet `± a ± b`. -/
def moment (a b : R) (k : ℕ) : R :=
  (a + b) ^ k + (a - b) ^ k + (-a + b) ^ k + (-a - b) ^ k

/-- **Symmetry protection.** The quartet moment is even in the off-line displacement `a`
(invariant under the functional-equation involution `a ↦ -a`).  Being even, it has no
first-order term: the first variation of the moment in the off-line displacement vanishes. -/
theorem moment_even (a b : R) (k : ℕ) : moment (-a) b k = moment a b k := by
  simp only [moment, neg_neg]
  ring

/-- The quartet moment is also even in `b` (the reality involution `b ↦ -b`). -/
theorem moment_even_b (a b : R) (k : ℕ) : moment a (-b) k = moment a b k := by
  simp only [moment]
  ring

/-- The odd-degree quartet moments vanish identically (functional-equation parity). -/
theorem moment_odd_eq_zero (a b : R) {k : ℕ} (hk : Odd k) : moment a b k = 0 := by
  unfold moment
  have h1 : (-a + b) = -(a - b) := by ring
  have h2 : (-a - b) = -(a + b) := by ring
  rw [h1, h2, hk.neg_pow, hk.neg_pow]
  ring

/-- The same protection for a sum of moments over *any* index set of `(displacement, b)`
pairs that all share a common off-line displacement `a`: evenness in `a` is preserved by
summation, so a sum of quartet moments is even in `a` too.  (This is the version that
applies to the full zero set: every zero contributes a quartet, all sharing the global
off-line-deformation parameter.) -/
theorem sum_moment_even {ι : Type*} (s : Finset ι) (a : R) (b : ι → R) (k : ℕ) :
    (∑ i ∈ s, moment (-a) (b i) k) = ∑ i ∈ s, moment a (b i) k := by
  refine Finset.sum_congr rfl ?_
  intro i _
  exact moment_even a (b i) k

end JensenLadder.SymmetryProtection
