import Mathlib.Tactic

/-!
# Davenport-Heilbronn multiplicativity fake gate

This file formalizes the finite arithmetic obstruction used by the
fake-family filter.

A single normalized Euler product coefficient stream must satisfy coprime
multiplicativity.  The Davenport-Heilbronn coefficient pattern already violates
that law at the coprime pair `(2, 3)`: its local values have
`a 2 = kappa`, `a 3 = -kappa`, and `a 6 = 1`, while multiplicativity would
force `a 6 = a 2 * a 3 = -kappa^2`.

This is not a proof of the carrier domination theorem and not a proof of RH.
It is a finite fake-gate: DH-style replays cannot instantiate a theorem row
that genuinely requires a single multiplicative Euler-product coefficient law.

Evidence class: proved finite arithmetic lemma.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace DHMultiplicityFakeGate

/-- Coprime multiplicativity for a real arithmetic coefficient stream. -/
def CoprimeMultiplicative (a : ℕ -> ℝ) : Prop :=
  ∀ m n : ℕ, Nat.Coprime m n -> a (m * n) = a m * a n

/-- Total multiplicativity, normalized at `1`. -/
def TotallyMultiplicative (a : ℕ -> ℝ) : Prop :=
  a 1 = 1 ∧ ∀ m n : ℕ, a (m * n) = a m * a n

/--
The finite Davenport-Heilbronn residue pattern at `1,2,3,6`.

The usual modulo-5 pattern gives `a 1 = 1`, `a 2 = kappa`, `a 3 = -kappa`,
and `a 6 = a 1 = 1`.
-/
def DHPattern236 (a : ℕ -> ℝ) (kappa : ℝ) : Prop :=
  a 1 = 1 ∧ a 2 = kappa ∧ a 3 = -kappa ∧ a 6 = 1

/-- The zeta unit coefficient stream is coprime multiplicative. -/
theorem zetaUnit_coprimeMultiplicative :
    CoprimeMultiplicative (fun _ : ℕ => (1 : ℝ)) := by
  intro _m _n _hcop
  simp

/-- The zeta unit coefficient stream is totally multiplicative. -/
theorem zetaUnit_totallyMultiplicative :
    TotallyMultiplicative (fun _ : ℕ => (1 : ℝ)) := by
  constructor
  · simp
  · intro _m _n
    simp

/--
The Davenport-Heilbronn finite pattern cannot satisfy coprime
multiplicativity.
-/
theorem not_coprimeMultiplicative_of_DHPattern236
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    ¬ CoprimeMultiplicative a := by
  intro hmul
  rcases h with ⟨_h1, h2, h3, h6⟩
  have hcop : Nat.Coprime 2 3 := by decide
  have hm := hmul 2 3 hcop
  norm_num at hm
  rw [h6, h2, h3] at hm
  ring_nf at hm
  nlinarith [sq_nonneg kappa]

/--
The same finite pattern also rules out total multiplicativity.
-/
theorem not_totallyMultiplicative_of_DHPattern236
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    ¬ TotallyMultiplicative a := by
  intro hmul
  exact not_coprimeMultiplicative_of_DHPattern236 h (by
    intro m n _hcop
    exact hmul.2 m n)

end DHMultiplicityFakeGate
end JensenLadder
