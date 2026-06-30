import GaloisForLFunctions.FriableAuxiliary

/-!
# Archimedean generator on finite prime Fourier modes

This file formalizes the prime-side derivative identity from
`archimedean-generator-axis-mode.md`:

`d/ds exp(-s * sum_p m_p log p) = -(sum_p m_p log p) * exp(-s * sum_p m_p log p)`.

It is the finite-support integer-mode skeleton of
`∂_s e_m = -(m · ell) e_m`.  It does not formalize the infinite torus, the
completed connection, or the archimedean Gamma/digamma residue.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The finite complex prime-log frequency `m · ell = sum_p m_p log p` for an
integer Fourier mode. -/
def primeLogFrequencyComplex (m : Nat.Primes →₀ ℤ) : ℂ :=
  m.sum fun p z => (z : ℂ) * (Real.log (p : ℕ) : ℂ)

/-- The analytic diagonal prime mode attached to a finite integer exponent vector. -/
def archimedeanPrimeMode (m : Nat.Primes →₀ ℤ) (s : ℂ) : ℂ :=
  Complex.exp (-(s * primeLogFrequencyComplex m))

/-- The archimedean `s`-generator acts diagonally on each finite prime Fourier
mode: `∂_s e_m = -(m · ell) e_m`. -/
theorem deriv_archimedeanPrimeMode (m : Nat.Primes →₀ ℤ) (s : ℂ) :
    deriv (archimedeanPrimeMode m) s =
      -primeLogFrequencyComplex m * archimedeanPrimeMode m s := by
  unfold archimedeanPrimeMode
  have hlin : HasDerivAt
      (fun z : ℂ => -(z * primeLogFrequencyComplex m))
      (-primeLogFrequencyComplex m) s := by
    have hid : HasDerivAt (fun z : ℂ => z) 1 s := hasDerivAt_id s
    simpa using (hid.mul_const (primeLogFrequencyComplex m)).neg
  rw [hlin.cexp.deriv]
  ring

end

end GaloisForLFunctions
