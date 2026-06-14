import JensenLadder.SquaredDeterminantSpectralProduct
import Mathlib.Tactic

/-!
# Finite chiral moment PSD certificate

This module formalizes the finite positivity row behind the chiral `T*T`
Stieltjes/Hankel gate.  A finite nonnegative squared spectrum has moments

```text
  m_k = sum_a E_a^k,
```

and every shifted Hankel quadratic form built from these moments is a sum of
squares:

```text
  sum_i sum_j c_i c_j m_{shift+i+j}
    = sum_a E_a^shift (sum_i c_i E_a^i)^2 >= 0.
```

This is a finite carrier certificate only.  It does not construct the zeta
carrier, does not identify the moments with completed explicit-formula source
data, does not prove determinant convergence, and does not prove RH.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantSpectralProduct

open scoped BigOperators

universe u

namespace FiniteSquaredSpectrum

/-- The `k`-th finite Stieltjes moment of a nonnegative squared spectrum. -/
noncomputable def moment (S : FiniteSquaredSpectrum.{u}) (k : ℕ) : ℝ := by
  letI := S.fintype
  exact ∑ a : S.Index, (S.energy a) ^ k

/--
The shifted Hankel quadratic form associated to the moment row
`m_k = sum_a E_a^k`.
-/
noncomputable def hankelQuadratic (S : FiniteSquaredSpectrum.{u}) (shift n : ℕ)
    (c : Fin n -> ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, c i * c j * S.moment (shift + i.val + j.val)

/--
The manifest square certificate for the shifted Hankel quadratic form.
-/
noncomputable def squareCertificate (S : FiniteSquaredSpectrum.{u}) (shift n : ℕ)
    (c : Fin n -> ℝ) : ℝ := by
  letI := S.fintype
  exact ∑ a : S.Index, (S.energy a) ^ shift *
    (∑ i : Fin n, c i * (S.energy a) ^ i.val) ^ 2

/-- One spectral atom expands the square certificate into the Hankel monomials. -/
lemma squareCertificate_expand_one (S : FiniteSquaredSpectrum.{u})
    (shift n : ℕ) (c : Fin n -> ℝ) (a : S.Index) :
    (S.energy a) ^ shift * (∑ i : Fin n, c i * (S.energy a) ^ i.val) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * c j * (S.energy a) ^ (shift + i.val + j.val) := by
  rw [sq]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp [pow_add]
  ring_nf

/--
The shifted Hankel quadratic form is exactly the square certificate.  This is
the finite algebraic core of the Stieltjes PSD gate.
-/
theorem hankelQuadratic_eq_squareCertificate (S : FiniteSquaredSpectrum.{u})
    (shift n : ℕ) (c : Fin n -> ℝ) :
    S.hankelQuadratic shift n c = S.squareCertificate shift n c := by
  classical
  letI := S.fintype
  calc
    S.hankelQuadratic shift n c
        = ∑ i : Fin n, ∑ j : Fin n, ∑ a : S.Index,
            c i * c j * (S.energy a) ^ (shift + i.val + j.val) := by
            simp [hankelQuadratic, moment, Finset.mul_sum]
    _ = ∑ a : S.Index, ∑ i : Fin n, ∑ j : Fin n,
            c i * c j * (S.energy a) ^ (shift + i.val + j.val) := by
            rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ a : S.Index,
                c i * c j * (S.energy a) ^ (shift + i.val + j.val)) =
                ∑ i : Fin n, ∑ a : S.Index, ∑ j : Fin n,
                c i * c j * (S.energy a) ^ (shift + i.val + j.val) by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
    _ = S.squareCertificate shift n c := by
            rw [squareCertificate]
            simp_rw [← squareCertificate_expand_one S shift n c]

/-- The square certificate is nonnegative for every coefficient vector. -/
theorem squareCertificate_nonnegative (S : FiniteSquaredSpectrum.{u})
    (shift n : ℕ) (c : Fin n -> ℝ) :
    0 <= S.squareCertificate shift n c := by
  classical
  simp [squareCertificate]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (pow_nonneg (S.nonnegative a) shift) (sq_nonneg _)

/--
Every finite shifted Hankel matrix built from the moments of a nonnegative
squared spectrum is positive semidefinite in quadratic-form form.
-/
theorem hankelQuadratic_nonnegative (S : FiniteSquaredSpectrum.{u})
    (shift n : ℕ) (c : Fin n -> ℝ) :
    0 <= S.hankelQuadratic shift n c := by
  rw [S.hankelQuadratic_eq_squareCertificate]
  exact S.squareCertificate_nonnegative shift n c

/--
The two standard finite Stieltjes moment tests: the ordinary Hankel form
`[m_{i+j}]` and the shifted Hankel form `[m_{i+j+1}]` are both positive
semidefinite in quadratic-form form.
-/
theorem stieltjesHankelPair_nonnegative (S : FiniteSquaredSpectrum.{u})
    (n : ℕ) (c0 c1 : Fin n -> ℝ) :
    0 <= S.hankelQuadratic 0 n c0 ∧
      0 <= S.hankelQuadratic 1 n c1 :=
  ⟨S.hankelQuadratic_nonnegative 0 n c0,
    S.hankelQuadratic_nonnegative 1 n c1⟩

end FiniteSquaredSpectrum

end SquaredDeterminantSpectralProduct
end JensenLadder
