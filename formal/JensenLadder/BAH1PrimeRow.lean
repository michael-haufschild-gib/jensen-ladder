import Mathlib.Tactic

/-!
# BAH1 finite prime-row algebra

This file formalizes the algebraic assembly of the finite direct-Suzuki prime
row for the `BAH1` candidate.  It does not prove the shifted-overlap integral
formulas, the finite support `{2,3,4}`, or the von Mangoldt values.  Those are
separate arithmetic/analysis rows.

Given supplied weights `w₂,w₃,w₄` and supplied symmetric overlap entries
`M_q,00`, `M_q,0S`, `M_q,SS`, the finite row is

```text
  Σ_{q∈{2,3,4}} w_q (M_q,00 u^2 + 2 M_q,0S u v + M_q,SS v^2).
```

Under the documented BAH1 zero rows `M_2,SS=M_3,SS=M_4,SS=M_4,00=0`, this
collapses to

```text
  C_00 u^2 + 2 C_0S u v.
```

## Honest scope

This is a finite algebra artifact for the BAH1 candidate, not a proof of the
multiplicative P2 row and not an RH proof.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

namespace JensenLadder
namespace BAH1PrimeRow

/-- A symmetric two-coordinate quadratic overlap
`M00*u^2 + 2*M0S*u*v + MSS*v^2`. -/
def overlap (M00 M0S MSS u v : ℝ) : ℝ :=
  M00 * u ^ 2 + 2 * M0S * u * v + MSS * v ^ 2

/-- The finite BAH1 prime row assembled from the `q=2,3,4` weighted overlap
matrices.  The weights stand for whatever arithmetic row is being replayed
(`Λ(q)/sqrt(q)` for zeta, or the corresponding fake/shuffled stream). -/
def finitePrimeRow
    (w2 w3 w4 : ℝ)
    (M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS : ℝ)
    (u v : ℝ) : ℝ :=
  w2 * overlap M2_00 M2_0S M2_SS u v
    + w3 * overlap M3_00 M3_0S M3_SS u v
    + w4 * overlap M4_00 M4_0S M4_SS u v

/-- The documented BAH1 `C_00` coefficient; the `q=4` diagonal contribution is
absent because the BAH1 formula has `M_4,00=0`. -/
def C00 (w2 w3 M2_00 M3_00 : ℝ) : ℝ :=
  w2 * M2_00 + w3 * M3_00

/-- The documented BAH1 `C_0S` coefficient. -/
def C0S (w2 w3 w4 M2_0S M3_0S M4_0S : ℝ) : ℝ :=
  w2 * M2_0S + w3 * M3_0S + w4 * M4_0S

/-- With the BAH1 zero rows supplied, the finite prime row has exactly the
documented `C_00*u^2 + 2*C_0S*u*v` shape. -/
theorem finitePrimeRow_eq_C00_C0S
    {w2 w3 w4 : ℝ}
    {M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS u v : ℝ}
    (h2SS : M2_SS = 0)
    (h3SS : M3_SS = 0)
    (h400 : M4_00 = 0)
    (h4SS : M4_SS = 0) :
    finitePrimeRow w2 w3 w4
        M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS u v =
      C00 w2 w3 M2_00 M3_00 * u ^ 2
        + 2 * C0S w2 w3 w4 M2_0S M3_0S M4_0S * u * v := by
  subst M2_SS
  subst M3_SS
  subst M4_00
  subst M4_SS
  simp [finitePrimeRow, overlap, C00, C0S]
  ring

/-- Under the BAH1 zero `SS` rows, the pure signal direction `(u=0)` has zero
finite prime row. -/
theorem finitePrimeRow_pureSignal_eq_zero
    {w2 w3 w4 : ℝ}
    {M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS v : ℝ}
    (h2SS : M2_SS = 0)
    (h3SS : M3_SS = 0)
    (h4SS : M4_SS = 0) :
    finitePrimeRow w2 w3 w4
        M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS 0 v = 0 := by
  subst M2_SS
  subst M3_SS
  subst M4_SS
  simp [finitePrimeRow, overlap]

/-- Therefore any nonzero finite BAH1 prime row with the documented zero `SS`
rows must keep a nonzero origin component. -/
theorem origin_component_ne_zero_of_finitePrimeRow_ne_zero
    {w2 w3 w4 : ℝ}
    {M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS u v : ℝ}
    (h2SS : M2_SS = 0)
    (h3SS : M3_SS = 0)
    (h4SS : M4_SS = 0)
    (hrow :
      finitePrimeRow w2 w3 w4
        M2_00 M2_0S M2_SS M3_00 M3_0S M3_SS M4_00 M4_0S M4_SS u v ≠ 0) :
    u ≠ 0 := by
  intro hu
  subst u
  exact hrow (finitePrimeRow_pureSignal_eq_zero h2SS h3SS h4SS)

end BAH1PrimeRow
end JensenLadder
