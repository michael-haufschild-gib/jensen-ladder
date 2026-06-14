import JensenLadder.ChiralMomentPSD
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-!
# Finite chiral Stieltjes trace identities

This module formalizes the finite logarithmic-derivative row behind the chiral
`T*T` Stieltjes gate.  For a finite nonnegative squared spectrum it proves the
scalar identities

```text
  -logDeriv (prod_i (E_i - w)) = sum_i 1 / (E_i - w),
  -logDeriv (prod_i (1 - w E_i)) = sum_i E_i / (1 - w E_i),
```

away from the corresponding finite spectrum.  Together with
`ChiralMomentPSD`, this gives the finite algebraic core:

```text
finite positive squared spectrum
  -> Stieltjes logarithmic derivative
  -> shifted Hankel moment PSD.
```

This file does not construct the zeta carrier, identify the finite trace with
completed explicit-formula source data, prove a limiting determinant identity,
or prove RH.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantSpectralProduct

open scoped BigOperators

universe u

namespace FiniteSquaredSpectrum

/-- The spectral product is off-spectrum at `w` if no factor `E_i - w`
vanishes. -/
def SpectralOffSpectrum (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : Prop :=
  ∀ i : S.Index, ((S.energy i : ℂ) - w) ≠ 0

/-- The finite spectral Stieltjes trace `sum_i (E_i - w)^{-1}`. -/
noncomputable def spectralResolventTrace
    (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : ℂ := by
  classical
  letI := S.fintype
  exact ∑ i : S.Index, (((S.energy i : ℂ) - w)⁻¹)

/-- Off-spectrum points are not zeros of the spectral determinant. -/
theorem determinant_ne_zero_of_spectralOffSpectrum
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.SpectralOffSpectrum w) :
    S.determinant w ≠ 0 := by
  classical
  letI := S.fintype
  unfold determinant
  exact Finset.prod_ne_zero_iff.mpr fun i _hi => hoff i

/--
The logarithmic derivative of the finite spectral determinant is the negative
Stieltjes trace.
-/
theorem logDeriv_determinant_eq_neg_spectralResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.SpectralOffSpectrum w) :
    logDeriv S.determinant w = -S.spectralResolventTrace w := by
  classical
  letI := S.fintype
  have h := logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ)
    (s := (Finset.univ : Finset S.Index))
    (f := fun i w => ((S.energy i : ℂ) - w))
    (x := w)
    (by
      intro i _hi
      exact hoff i)
    (by
      intro i _hi
      fun_prop)
  calc
    logDeriv S.determinant w
        = ∑ i : S.Index, -1 / ((S.energy i : ℂ) - w) := by
            simpa [determinant, logDeriv_apply] using h
    _ = -S.spectralResolventTrace w := by
            simp [spectralResolventTrace, div_eq_mul_inv]

/-- Spectral Stieltjes form with the conventional leading minus sign. -/
theorem neg_logDeriv_determinant_eq_spectralResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.SpectralOffSpectrum w) :
    -logDeriv S.determinant w = S.spectralResolventTrace w := by
  rw [S.logDeriv_determinant_eq_neg_spectralResolventTrace hoff]
  simp

/-- Derivative form of the finite spectral Stieltjes identity. -/
theorem deriv_determinant_eq_neg_mul_spectralResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.SpectralOffSpectrum w) :
    deriv S.determinant w =
      -S.determinant w * S.spectralResolventTrace w := by
  have hlog := S.logDeriv_determinant_eq_neg_spectralResolventTrace hoff
  have hdet := S.determinant_ne_zero_of_spectralOffSpectrum hoff
  rw [logDeriv_apply] at hlog
  calc
    deriv S.determinant w
        = (deriv S.determinant w / S.determinant w) * S.determinant w := by
            field_simp [hdet]
    _ = (-S.spectralResolventTrace w) * S.determinant w := by
            rw [hlog]
    _ = -S.determinant w * S.spectralResolventTrace w := by
            ring

/-!
## Fredholm normalization
-/

/-- Finite Fredholm determinant `prod_i (1 - w E_i)`. -/
noncomputable def fredholmDeterminant
    (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : ℂ := by
  letI := S.fintype
  exact ∏ i : S.Index, (1 - w * (S.energy i : ℂ))

/-- The Fredholm product is off-spectrum at `w` if no factor `1 - w E_i`
vanishes. -/
def FredholmOffSpectrum (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : Prop :=
  ∀ i : S.Index, (1 - w * (S.energy i : ℂ)) ≠ 0

/-- The finite Fredholm Stieltjes trace `sum_i E_i / (1 - w E_i)`. -/
noncomputable def fredholmResolventTrace
    (S : FiniteSquaredSpectrum.{u}) (w : ℂ) : ℂ := by
  classical
  letI := S.fintype
  exact ∑ i : S.Index, (S.energy i : ℂ) / (1 - w * (S.energy i : ℂ))

/-- Off-spectrum points are not zeros of the finite Fredholm determinant. -/
theorem fredholmDeterminant_ne_zero_of_fredholmOffSpectrum
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.FredholmOffSpectrum w) :
    S.fredholmDeterminant w ≠ 0 := by
  classical
  letI := S.fintype
  unfold fredholmDeterminant
  exact Finset.prod_ne_zero_iff.mpr fun i _hi => hoff i

/--
The logarithmic derivative of the finite Fredholm determinant is the negative
Fredholm Stieltjes trace.
-/
theorem logDeriv_fredholmDeterminant_eq_neg_fredholmResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.FredholmOffSpectrum w) :
    logDeriv S.fredholmDeterminant w = -S.fredholmResolventTrace w := by
  classical
  letI := S.fintype
  have h := logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ)
    (s := (Finset.univ : Finset S.Index))
    (f := fun i w => 1 - w * (S.energy i : ℂ))
    (x := w)
    (by
      intro i _hi
      exact hoff i)
    (by
      intro i _hi
      fun_prop)
  calc
    logDeriv S.fredholmDeterminant w
        = ∑ i : S.Index,
            (-(S.energy i : ℂ)) / (1 - w * (S.energy i : ℂ)) := by
            simpa [fredholmDeterminant, logDeriv_apply] using h
    _ = -S.fredholmResolventTrace w := by
            simp [fredholmResolventTrace, neg_div]

/-- Fredholm Stieltjes form with the conventional leading minus sign. -/
theorem neg_logDeriv_fredholmDeterminant_eq_fredholmResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.FredholmOffSpectrum w) :
    -logDeriv S.fredholmDeterminant w = S.fredholmResolventTrace w := by
  rw [S.logDeriv_fredholmDeterminant_eq_neg_fredholmResolventTrace hoff]
  simp

/-- Derivative form of the finite Fredholm Stieltjes identity. -/
theorem deriv_fredholmDeterminant_eq_neg_mul_fredholmResolventTrace
    (S : FiniteSquaredSpectrum.{u}) {w : ℂ}
    (hoff : S.FredholmOffSpectrum w) :
    deriv S.fredholmDeterminant w =
      -S.fredholmDeterminant w * S.fredholmResolventTrace w := by
  have hlog := S.logDeriv_fredholmDeterminant_eq_neg_fredholmResolventTrace hoff
  have hdet := S.fredholmDeterminant_ne_zero_of_fredholmOffSpectrum hoff
  rw [logDeriv_apply] at hlog
  calc
    deriv S.fredholmDeterminant w
        = (deriv S.fredholmDeterminant w / S.fredholmDeterminant w) *
            S.fredholmDeterminant w := by
            field_simp [hdet]
    _ = (-S.fredholmResolventTrace w) * S.fredholmDeterminant w := by
            rw [hlog]
    _ = -S.fredholmDeterminant w * S.fredholmResolventTrace w := by
            ring

/-- At `w = 0`, the Fredholm Stieltjes trace is the first finite moment. -/
theorem fredholmResolventTrace_zero_eq_moment_one
    (S : FiniteSquaredSpectrum.{u}) :
    S.fredholmResolventTrace 0 = (S.moment 1 : ℂ) := by
  classical
  letI := S.fintype
  simp [fredholmResolventTrace, moment]

end FiniteSquaredSpectrum

end SquaredDeterminantSpectralProduct
end JensenLadder
