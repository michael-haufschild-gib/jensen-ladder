import GaloisForLFunctions.Core

/-!
# Finite congruence pencils

This file formalizes the finite algebraic identity behind the DeWitt/no-margin
congruence-pencil comparison. If `B` is a chosen square root/congruence factor
for the positive block `A = B * B`, and `Binv` is a two-sided inverse of `B`,
then the normalized pencil conjugates back to the original pencil:

`B * (lam * I - Binv * P * Binv) * B = lam * (B * B) - P`.

No spectral theorem, norm formula, limiting Hankel carrier, or RH/de
Bruijn-Newman statement is formalized here.
-/

open Matrix

namespace GaloisForLFunctions

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable section

/-- **Finite congruence-pencil factorization.** Given a square matrix `B` with
two-sided inverse `Binv`, the normalized perturbation `Binv * P * Binv`
conjugates back to the original pencil `lam * (B * B) - P`. This is the exact
finite algebraic identity underlying the paper notation
`A^(1/2) (lam I - A^(-1/2) P A^(-1/2)) A^(1/2) = lam A - P`.
-/
theorem congruencePencil_factorization (R : Type*) [CommRing R]
    (B Binv P : Matrix n n R) (lam : R)
    (hL : B * Binv = 1) (hR : Binv * B = 1) :
    B * (lam • (1 : Matrix n n R) - Binv * P * Binv) * B = lam • (B * B) - P := by
  have hscale : B * (lam • (1 : Matrix n n R)) * B = lam • (B * B) := by
    simp
  have hcancel : B * (Binv * P * Binv) * B = P := by
    calc
      B * (Binv * P * Binv) * B = (B * Binv) * P * (Binv * B) := by
        simp only [mul_assoc]
      _ = P := by simp [hL, hR]
  calc
    B * (lam • (1 : Matrix n n R) - Binv * P * Binv) * B
        = B * (lam • (1 : Matrix n n R)) * B - B * (Binv * P * Binv) * B := by
          rw [mul_sub]
          rw [sub_mul]
    _ = lam • (B * B) - P := by rw [hscale, hcancel]

/-- Additive rearrangement of `congruencePencil_factorization`: after adding
the prime block `P`, the congruence-normalized pencil recovers the scaled
positive block `lam * (B * B)`. -/
theorem congruencePencil_add_primeBlock (R : Type*) [CommRing R]
    (B Binv P : Matrix n n R) (lam : R)
    (hL : B * Binv = 1) (hR : Binv * B = 1) :
    B * (lam • (1 : Matrix n n R) - Binv * P * Binv) * B + P = lam • (B * B) := by
  rw [congruencePencil_factorization R B Binv P lam hL hR]
  abel

end

end GaloisForLFunctions
