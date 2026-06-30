import GaloisForLFunctions.Core

/-!
# Functional-equation pullback and the derivative time-reversal

This file formalizes the elementary chain-rule skeleton behind the completed
connection card's PT statement.  Pulling a function back by the functional
equation involution `sigma(s)=1-s` conjugates the `s`-derivative to its negative.

It does not formalize the completed connection category, Hilbert-Polya
operators, unitary holonomy, or RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Pull a scalar function back along the functional-equation involution
`sigma(s)=1-s`. -/
def fePullback (f : ℂ → ℂ) : ℂ → ℂ := fun s => f (sigma s)

@[simp] theorem fePullback_apply (f : ℂ → ℂ) (s : ℂ) :
    fePullback f s = f (sigma s) := rfl

/-- Pullback along the FE involution is itself an involution. -/
theorem fePullback_involutive (f : ℂ → ℂ) : fePullback (fePullback f) = f := by
  funext s
  simp [fePullback, sigma]

/-- The derivative of the FE involution `s ↦ 1-s` is `-1`. -/
theorem hasDerivAt_sigma (s : ℂ) : HasDerivAt sigma (-1) s := by
  unfold sigma
  simpa using (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub (hasDerivAt_id s)

/-- Chain-rule form: pulling back by `sigma` negates the derivative. -/
theorem hasDerivAt_fePullback {f : ℂ → ℂ} {s f' : ℂ}
    (h : HasDerivAt f f' (sigma s)) :
    HasDerivAt (fePullback f) (-f') s := by
  have hcomp := h.comp s (hasDerivAt_sigma s)
  simpa [fePullback, neg_mul, mul_comm] using hcomp

/-- Derivative form of the FE pullback chain rule. -/
theorem deriv_fePullback_eq_neg (f : ℂ → ℂ) (s : ℂ)
    (h : DifferentiableAt ℂ f (sigma s)) :
    deriv (fePullback f) s = -deriv f (sigma s) := by
  exact (hasDerivAt_fePullback (h.hasDerivAt)).deriv

/-- Evaluate the derivative of the FE pullback at the reflected point. -/
theorem deriv_fePullback_at_sigma_eq_neg (f : ℂ → ℂ) (s : ℂ)
    (h : DifferentiableAt ℂ f s) :
    deriv (fePullback f) (sigma s) = -deriv f s := by
  have hs : sigma (sigma s) = s := sigma_involutive s
  have h' : DifferentiableAt ℂ f (sigma (sigma s)) := by
    simpa [hs] using h
  simpa [hs] using deriv_fePullback_eq_neg f (sigma s) h'

/-- Conjugation form of time reversal:
`sigma^* d/ds sigma^* = - d/ds` on functions differentiable at `s`. -/
theorem fePullback_deriv_fePullback_eq_neg_deriv (f : ℂ → ℂ) (s : ℂ)
    (h : DifferentiableAt ℂ f s) :
    fePullback (fun z => deriv (fePullback f) z) s = -deriv f s := by
  change deriv (fePullback f) (sigma s) = -deriv f s
  exact deriv_fePullback_at_sigma_eq_neg f s h

end

end GaloisForLFunctions
