import Mathlib

/-!
# A two-prime gluing witness (Tier A)

This file formalizes the finite matrix witness from
`docs/drafts/pipeline/2-fully-proven/c3-gluing-invariants-bridge.md`.

The point is deliberately small: two pairs of `2 × 2` rational matrices have
the same per-prime conjugacy data, but differ as a joint pair because the word
trace `tr(A₂ A₃)` changes. This machine-checks the concrete algebraic witness
for "joint gluing is strictly finer than per-prime data"; it does not formalize
the Procesi/Artin invariant-theory import or the C5★ reduction.
-/

namespace GaloisForLFunctions

open Matrix

/-- The rational `2 × 2` matrices used in the gluing witness. -/
abbrev Mat2Rat := Matrix (Fin 2) (Fin 2) ℚ

def gluingA2 : Mat2Rat := ![![1, 1], ![0, 1]]
def gluingA3 : Mat2Rat := ![![1, 0], ![1, 1]]
def gluingH : Mat2Rat := ![![2, 0], ![0, 1]]
def gluingHinv : Mat2Rat := ![![(1 / 2 : ℚ), 0], ![0, 1]]
def gluingB2 : Mat2Rat := gluingA2
def gluingB3 : Mat2Rat := ![![1, 0], ![(1 / 2 : ℚ), 1]]

theorem gluingH_mul_Hinv : gluingH * gluingHinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gluingH, gluingHinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem gluingHinv_mul_H : gluingHinv * gluingH = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gluingH, gluingHinv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second matrix of the `B` pair is conjugate to the second matrix of the
`A` pair, so the two pairs have identical per-prime data at this prime. -/
theorem gluingB3_eq_conj : gluingH * gluingA3 * gluingHinv = gluingB3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gluingH, gluingA3, gluingHinv, gluingB3, Matrix.mul_apply, Fin.sum_univ_two]

theorem gluing_trace_A2A3 : (gluingA2 * gluingA3).trace = 3 := by
  norm_num [gluingA2, gluingA3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem gluing_trace_B2B3 : (gluingB2 * gluingB3).trace = (5 / 2 : ℚ) := by
  norm_num [gluingB2, gluingA2, gluingB3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- The word trace distinguishes the two joint pairs. -/
theorem gluing_trace_ne : (gluingA2 * gluingA3).trace ≠ (gluingB2 * gluingB3).trace := by
  rw [gluing_trace_A2A3, gluing_trace_B2B3]
  norm_num

/-- No single simultaneous conjugacy can carry `(A₂,A₃)` to `(B₂,B₃)`.

The statement uses explicit left/right matrices `P,Q` with `Q * P = 1`; this is
enough for the trace-cycling obstruction. Any genuine invertible conjugacy gives
such data. -/
theorem gluing_not_jointly_conjugate
    (P Q : Mat2Rat) (hQP : Q * P = 1)
    (h2 : P * gluingA2 * Q = gluingB2) (h3 : P * gluingA3 * Q = gluingB3) :
    False := by
  have htrace : (gluingB2 * gluingB3).trace = (gluingA2 * gluingA3).trace := by
    rw [← h2, ← h3]
    calc
      (P * gluingA2 * Q * (P * gluingA3 * Q)).trace
          = (P * gluingA2 * (Q * P) * gluingA3 * Q).trace := by
              simp only [mul_assoc]
      _ = (P * gluingA2 * 1 * gluingA3 * Q).trace := by rw [hQP]
      _ = (P * (gluingA2 * gluingA3) * Q).trace := by simp only [mul_assoc, mul_one]
      _ = (Q * P * (gluingA2 * gluingA3)).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (1 * (gluingA2 * gluingA3)).trace := by rw [hQP]
      _ = (gluingA2 * gluingA3).trace := by simp
  exact gluing_trace_ne htrace.symm

/-- Packaged C3 witness: per-prime conjugacy agrees, but the joint pair is not
simultaneously conjugate. -/
theorem gluing_per_prime_same_but_joint_distinct :
    gluingB2 = gluingA2 ∧
      gluingH * gluingHinv = 1 ∧
      gluingHinv * gluingH = 1 ∧
      gluingH * gluingA3 * gluingHinv = gluingB3 ∧
      (∀ P Q : Mat2Rat,
        Q * P = 1 →
          P * gluingA2 * Q = gluingB2 →
            P * gluingA3 * Q = gluingB3 → False) := by
  exact ⟨rfl, gluingH_mul_Hinv, gluingHinv_mul_H, gluingB3_eq_conj,
    gluing_not_jointly_conjugate⟩

end GaloisForLFunctions
