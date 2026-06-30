import GaloisForLFunctions.ZeroEstimate
import GaloisForLFunctions.FriableAuxiliary

open scoped BigOperators

/-!
# Exponential-sum order bound for the uniform zero estimate

This file adds the analytic wrapper for
`docs/drafts/pipeline/2-fully-proven/zero-estimate-uniformity.md`: a nonzero
finite exponential sum with `n` distinct frequencies has a nonzero derivative
of order `< n` at every point. Combined with the Vandermonde core in
`ZeroEstimate.lean`, this is the formal version of the card's multiplicity
argument.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A finite exponential sum `Σ_j c_j exp(s μ_j)`. -/
def exponentialSum {n : ℕ} (μ c : Fin n → ℂ) (s : ℂ) : ℂ :=
  ∑ j : Fin n, c j * Complex.exp (s * μ j)

private lemma iteratedDeriv_exp_mul (T : ℕ) (μ s : ℂ) :
    iteratedDeriv T (fun z : ℂ => Complex.exp (z * μ)) s =
      μ ^ T * Complex.exp (s * μ) := by
  have h := iteratedDeriv_exp_neg_mul_log T (-μ) s
  simpa using h

private lemma contDiff_exp_mul (T : ℕ) (μ s : ℂ) :
    ContDiffAt ℂ (T : WithTop ℕ∞) (fun z : ℂ => Complex.exp (z * μ)) s := by
  have h := contDiff_exp_neg_mul_log T (-μ) s
  simpa using h

private lemma iteratedDeriv_exponentialSum {n : ℕ}
    (T : ℕ) (μ c : Fin n → ℂ) (s : ℂ) :
    iteratedDeriv T (fun z : ℂ => exponentialSum μ c z) s =
      ∑ j : Fin n, c j * (μ j) ^ T * Complex.exp (s * μ j) := by
  unfold exponentialSum
  have hfun :
      (fun z : ℂ => ∑ j : Fin n, c j * Complex.exp (z * μ j)) =
        (∑ j : Fin n, fun z : ℂ => c j * Complex.exp (z * μ j)) := by
    funext z
    simp [Finset.sum_apply]
  rw [hfun]
  rw [iteratedDeriv_sum]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [iteratedDeriv_const_mul]
    · rw [iteratedDeriv_exp_mul]
      ring
    · exact contDiff_exp_mul T (μ j) s
  · intro j _
    have hc : ContDiffAt ℂ (T : WithTop ℕ∞) (fun _z : ℂ => c j) s := contDiffAt_const
    exact hc.mul (contDiff_exp_mul T (μ j) s)

/-- **Exponential-sum order bound.** At `n` distinct frequencies, a nonzero
coefficient vector has a nonzero derivative among orders `0, ..., n-1` at any
base point. This is the analytic wrapper around
`vandermonde_initial_moment_nonzero_of_nonzero_coeff`. -/
theorem exponentialSum_has_nonzero_iteratedDeriv_lt_card {n : ℕ} {μ c : Fin n → ℂ}
    (hμ : Function.Injective μ) (hc : c ≠ 0) (s₀ : ℂ) :
    ∃ k : Fin n, iteratedDeriv (k : ℕ) (fun z : ℂ => exponentialSum μ c z) s₀ ≠ 0 := by
  let c₀ : Fin n → ℂ := fun j => c j * Complex.exp (s₀ * μ j)
  have hc₀ : c₀ ≠ 0 := by
    intro hzero
    apply hc
    funext j
    have hj : c₀ j = 0 := by
      simpa using congrFun hzero j
    exact (mul_eq_zero.mp hj).resolve_right (Complex.exp_ne_zero (s₀ * μ j))
  rcases vandermonde_initial_moment_nonzero_of_nonzero_coeff hμ hc₀ with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro hder
  apply hk
  calc
    ∑ j : Fin n, c₀ j * (μ j) ^ (k : ℕ)
        = ∑ j : Fin n, c j * (μ j) ^ (k : ℕ) * Complex.exp (s₀ * μ j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [c₀]
            ring
    _ = iteratedDeriv (k : ℕ) (fun z : ℂ => exponentialSum μ c z) s₀ := by
            rw [iteratedDeriv_exponentialSum]
    _ = 0 := hder

end

end GaloisForLFunctions
