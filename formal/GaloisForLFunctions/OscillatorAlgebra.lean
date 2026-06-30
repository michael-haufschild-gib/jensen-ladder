import GaloisForLFunctions.Core

/-!
# Oscillator algebra skeleton: the free `sl₂` commutators (Tier A)

This file formalizes the elementary algebraic core of
`docs/drafts/secular-positivity-hierarchy.md` §§20–22.  In the monomial
coefficient basis, multiplication by `u²`, the second derivative, and the
Euler/weight operator `u∂ᵤ + 1/2` satisfy the oscillator commutators

* `[X,Y] = -4H`,
* `[H,X] = 2X`,
* `[H,Y] = -2Y`.

This is only the free algebraic skeleton of the metaplectic/oscillator story.
It does not formalize the Weil representation, theta modularity, hard
Lefschetz, Hodge--Riemann positivity, `Q_W`, or RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Multiplication by `u²` on coefficient sequences:
if `a n` is the coefficient of `u^n`, then `(oscX a) n` is the coefficient
after multiplying by `u²`. -/
def oscX (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if 2 ≤ n then a (n - 2) else 0

/-- The second derivative on coefficient sequences:
`∂²(u^(n+2)) = (n+2)(n+1)u^n`. -/
def oscY (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * a (n + 2)

/-- The Euler/weight operator `u∂ᵤ + 1/2` on coefficient sequences. -/
def oscH (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => ((n : ℂ) + (1 / 2 : ℂ)) * a n

/-- Commutator of two coefficient-sequence operators. -/
def oscComm (A B : (ℕ → ℂ) → (ℕ → ℂ)) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => A (B a) n - B (A a) n

/-- The oscillator relation `[X,Y] = -4H`, checked coefficientwise on the monomial basis. -/
theorem osc_comm_XY_apply (a : ℕ → ℂ) (n : ℕ) :
    oscComm oscX oscY a n = -4 * oscH a n := by
  unfold oscComm oscX oscY oscH
  by_cases h : 2 ≤ n
  · simp [h, Nat.sub_add_cancel h]
    ring
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> simp <;> ring

/-- The oscillator relation `[H,X] = 2X`, checked coefficientwise on the monomial basis. -/
theorem osc_comm_HX_apply (a : ℕ → ℂ) (n : ℕ) :
    oscComm oscH oscX a n = 2 * oscX a n := by
  unfold oscComm oscX oscH
  by_cases h : 2 ≤ n
  · simp [h]
    ring
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> simp

/-- The oscillator relation `[H,Y] = -2Y`, checked coefficientwise on the monomial basis. -/
theorem osc_comm_HY_apply (a : ℕ → ℂ) (n : ℕ) :
    oscComm oscH oscY a n = -2 * oscY a n := by
  unfold oscComm oscY oscH
  simp
  ring

end

end GaloisForLFunctions
