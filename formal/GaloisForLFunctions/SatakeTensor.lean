import GaloisForLFunctions.Core
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Finite Satake tensor products (Tier A diagonal skeleton)

`automorphic-continent-rankin-selberg-ramanujan.md` §3 says that the local Satake parameters of a
Rankin-Selberg tensor product are the pairwise products `{α_i β_j}`. This file formalizes the finite
diagonal-matrix skeleton of that statement:

* the Kronecker product of two diagonal Satake matrices is diagonal with entries `α_i β_j`;
* the finite local Euler factor attached to those tensor parameters is the double product over
  pairwise products.

It does not formalize automorphic Rankin-Selberg theory, diagonalizability/conjugacy for arbitrary
operators, Lyapunov spectra, or any analytic continuation statement.
-/

open scoped BigOperators Kronecker

namespace GaloisForLFunctions

noncomputable section

/-- Pairwise products of two finite Satake-parameter lists. -/
def satakeTensorParameters {m n : Type*} (α : m → ℂ) (β : n → ℂ) : m × n → ℂ :=
  fun ij => α ij.1 * β ij.2

/-- The finite Euler factor determined by a list of Satake parameters. -/
def satakeLocalFactor {ι : Type*} [Fintype ι] (α : ι → ℂ) (x : ℂ) : ℂ :=
  ∏ i, (1 - α i * x)⁻¹

/-- The Kronecker tensor of diagonal Satake matrices has the pairwise-product Satake parameters on
its diagonal. This is the finite diagonal skeleton of "Satake parameters tensor by pairwise
products." -/
theorem satakeTensor_diagonal {m n : Type*} [DecidableEq m] [DecidableEq n]
    (α : m → ℂ) (β : n → ℂ) :
    (Matrix.diagonal α ⊗ₖ Matrix.diagonal β : Matrix (m × n) (m × n) ℂ)
      = Matrix.diagonal (satakeTensorParameters α β) := by
  rw [Matrix.diagonal_kronecker_diagonal]
  rfl

/-- The local factor attached to tensor-product Satake parameters is the double product over
pairwise products. This is the finite local-factor skeleton of Rankin-Selberg `⊗`. -/
theorem satakeLocalFactor_tensor {m n : Type*} [Fintype m] [Fintype n]
    (α : m → ℂ) (β : n → ℂ) (x : ℂ) :
    satakeLocalFactor (satakeTensorParameters α β) x
      = ∏ i, ∏ j, (1 - (α i * β j) * x)⁻¹ := by
  unfold satakeLocalFactor satakeTensorParameters
  exact Fintype.prod_prod_type' (fun i j => (1 - α i * β j * x)⁻¹)

end

end GaloisForLFunctions
