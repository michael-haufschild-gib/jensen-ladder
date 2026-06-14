import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Xi Jensen section convention

This file fixes the actual finite-section convention used by the Jensen-ladder
program.

The input `M k` is the even moment sequence of the classical xi/theta kernel.
With `X = w^2`, the completed xi Taylor convention is

```text
Xi(w) = sum_{k >= 0} (-1)^k M k / (2k)! * w^(2k),
```

so the corresponding `X`-series coefficient is

```text
a_k = (-1)^k M k / (2k)!.
```

The finite normalized Jensen section is

```text
J_d[Xi](X) = sum_{k=0}^d ((d)_k / d^k) * a_k * X^k.
```

Here `(d)_k` is the falling factorial `d * (d-1) * ... * (d-k+1)`.
The polynomial in the original variable `w` is `J_d[Xi](w^2)`.

This is only the convention layer: no moment estimates, no Sturm certificate,
and no RH claim are made here.  Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

namespace JensenLadder
namespace XiJensen

open scoped BigOperators

noncomputable section

/-- Falling factorial `(d)_k = d * (d-1) * ... * (d-k+1)`, with
natural-number subtraction saturating after `k > d`. -/
def fallingFactorial (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (d - k) * fallingFactorial d k

/-- The xi even Taylor coefficient in the variable `X = w^2`.

If `M k` is the even moment of the xi/theta kernel, then
`Xi(w) = sum k, xiTaylorCoeff M k * w^(2*k)`. -/
def xiTaylorCoeff (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * M k / (Nat.factorial (2 * k) : ℝ)

/-- Jensen normalization multiplier `((d)_k / d^k)`.

For the section `J_d[Xi]`, this is only used on `k <= d`; in particular the
`d = 0` section contains only the `k = 0` term. -/
def jensenWeight (d k : ℕ) : ℝ :=
  (fallingFactorial d k : ℝ) / (d : ℝ) ^ k

/-- Coefficient of `X^k` in the normalized xi Jensen section `J_d[Xi](X)`. -/
def xiJensenCoeff (M : ℕ → ℝ) (d k : ℕ) : ℝ :=
  jensenWeight d k * xiTaylorCoeff M k

/-- Raw Taylor truncation in the variable `X = w^2`, before Jensen weighting. -/
def xiTaylorSectionX (M : ℕ → ℝ) (d : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (d + 1)) fun k =>
    Polynomial.C (xiTaylorCoeff M k) * (Polynomial.X : Polynomial ℝ) ^ k

/-- The actual normalized xi Jensen section in the variable `X = w^2`. -/
def xiJensenSectionX (M : ℕ → ℝ) (d : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (d + 1)) fun k =>
    Polynomial.C (xiJensenCoeff M d k) * (Polynomial.X : Polynomial ℝ) ^ k

/-- The square-variable polynomial used to pass from `X` back to `w`. -/
def squareVariable : Polynomial ℝ :=
  (Polynomial.X : Polynomial ℝ) ^ (2 : ℕ)

/-- The normalized xi Jensen section in the original even variable `w`.

This is `J_d[Xi](w^2)`, i.e. `xiJensenSectionX M d` composed with `X^2`.
-/
def xiJensenSectionW (M : ℕ → ℝ) (d : ℕ) : Polynomial ℝ :=
  (xiJensenSectionX M d).comp squareVariable

end

end XiJensen
end JensenLadder
