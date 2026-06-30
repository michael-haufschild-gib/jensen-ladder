import Mathlib

/-!
# Secular Newton-duality: the power-sum face and the elementary-symmetric face are one object (Tier A)

Formalizes the algebraic core of `docs/drafts/secular-positivity-hierarchy.md` §1 / Theorem 1:
the **two faces** of the secular spectrum are Newton-dual. For a finite truncation of the spectrum,
modelled by a family `f : Fin n → ℂ` (the values `tᵢ`, e.g. squared-zero reciprocals):

* the **power-sum (Hankel / resolvent / Pick) face** is `secularPowerSum f k = Σ_i (f i)^k`
  — the moments behind `m(z)=Σ_i (tᵢ−z)⁻¹` (cf. `CarrierPickKernel.lean`);
* the **elementary-symmetric (Toeplitz / Pólya-frequency) face** is `secularESymm f k`
  — the coefficients behind `∏_i (X − tᵢ)` (cf. the `ξ`-coefficients `cₙ = ξ(½)·eₙ`).

`secular_newton` is Newton's identity tying them, obtained by evaluating mathlib's symmetric-function
identity `MvPolynomial.psum_eq_mul_esymm_sub_sum` at `f`. Hence the two faces determine each other:
they are one object, as certified numerically (`computations/secular_positivity_hierarchy/`, to 5·10⁻²⁶).

Elementary algebra over a finite family. No zero, no RH, no positivity is formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators
open Finset

variable {n : ℕ}

/-- The power-sum (Hankel / resolvent) face of a finite secular spectrum `f`. -/
def secularPowerSum (f : Fin n → ℂ) (k : ℕ) : ℂ := ∑ i, f i ^ k

/-- The elementary-symmetric (Toeplitz / Pólya-frequency) face of a finite secular spectrum `f`. -/
def secularESymm (f : Fin n → ℂ) (k : ℕ) : ℂ :=
  (MvPolynomial.aeval f) (MvPolynomial.esymm (Fin n) ℂ k)

/-- The power-sum face is the evaluation of the symmetric polynomial `psum`. -/
theorem secularPowerSum_eq_aeval (f : Fin n → ℂ) (k : ℕ) :
    secularPowerSum f k = (MvPolynomial.aeval f) (MvPolynomial.psum (Fin n) ℂ k) := by
  rw [secularPowerSum, MvPolynomial.psum, map_sum]
  simp [map_pow, MvPolynomial.aeval_X]

/-- The elementary-symmetric face is the `k`-th elementary symmetric of the family, concretely. -/
theorem secularESymm_eq_sum (f : Fin n → ℂ) (k : ℕ) :
    secularESymm f k = ∑ t ∈ univ.powersetCard k, ∏ i ∈ t, f i := by
  rw [secularESymm, MvPolynomial.esymm, map_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [map_prod]
  simp [MvPolynomial.aeval_X]

/-- **Secular Newton-duality.** For every `k > 0`, the power-sum face and the elementary-symmetric
face of a finite secular spectrum satisfy Newton's identity; hence each determines the other. The
Hankel/resolvent (power-sum) face and the Toeplitz/PF (elementary-symmetric) face are one object. -/
theorem secular_newton (f : Fin n → ℂ) (k : ℕ) (hk : 0 < k) :
    secularPowerSum f k =
      (-1) ^ (k + 1) * (k : ℂ) * secularESymm f k -
        ∑ a ∈ (antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
          (-1) ^ a.1 * secularESymm f a.1 * secularPowerSum f a.2 := by
  have key := congrArg (MvPolynomial.aeval f)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k hk)
  rw [secularPowerSum_eq_aeval, key]
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    secularESymm, ← secularPowerSum_eq_aeval]

end

end GaloisForLFunctions
