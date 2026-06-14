import Mathlib.Tactic

/-!
# Finite residual Schur selector

This module formalizes the finite diagonal-transverse Schur row behind the
post-anomaly residual selector.  After the universal, source-blind edge anomaly
has been quotiented away, a finite residual carrier should be tested in block
form

```text
  Q = [ q   b* ]
      [ b   C  ],
```

relative to a declared zero-blind line.  In a basis that diagonalizes the
finite self-adjoint transverse block `C`, the Schur function is

```text
  Phi(E) = q - E - sum_i b_i^2 / (lambda_i - E).
```

For `E` below the transverse diagonal, `Phi(E)=0` is equivalent to the finite
block eigen-equations for the vector with line component `1` and transverse
coordinates

```text
  eta_i = - b_i / (lambda_i - E).
```

This is a finite carrier consumer only.  It does not construct the zeta
carrier, does not prove an anomaly quotient, does not prove fake-family
failure, and does not prove RH.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ResidualSchurSelector

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/--
A finite Schur block after diagonalizing the transverse self-adjoint part.

`q` is the line-line entry, `transverse i` is the `i`-th transverse eigenvalue,
and `coupling i` is the coupling from the declared line to that transverse
mode.
-/
structure DiagonalSchurBlock (ι : Type*) [Fintype ι] where
  q : ℝ
  transverse : ι -> ℝ
  coupling : ι -> ℝ

namespace DiagonalSchurBlock

/-- The residual Schur function `Phi(E)`. -/
noncomputable def schur (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  B.q - E - ∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E)

/-- The transverse coordinates of the eigenvector with line component `1`. -/
noncomputable def eta (B : DiagonalSchurBlock ι) (E : ℝ) (i : ι) : ℝ :=
  -B.coupling i / (B.transverse i - E)

/-- The center equation residual for the vector `(1, eta)`. -/
noncomputable def centerResidual (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  B.q + ∑ i : ι, B.coupling i * B.eta E i - E

/-- The `i`-th transverse equation residual for the vector `(1, eta)`. -/
noncomputable def transverseResidual (B : DiagonalSchurBlock ι) (E : ℝ)
    (i : ι) : ℝ :=
  B.coupling i + B.transverse i * B.eta E i - E * B.eta E i

/-- `E` lies strictly below every transverse diagonal entry. -/
def BelowTransverse (B : DiagonalSchurBlock ι) (E : ℝ) : Prop :=
  ∀ i : ι, E < B.transverse i

/-- A below-transverse point has no vanishing Schur denominator. -/
theorem denom_ne_of_below (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) (i : ι) :
    B.transverse i - E ≠ 0 := by
  have hpos : 0 < B.transverse i - E := sub_pos.mpr (hbelow i)
  exact ne_of_gt hpos

/-- The center equation residual is exactly the Schur function. -/
theorem centerResidual_eq_schur (B : DiagonalSchurBlock ι) (E : ℝ) :
    B.centerResidual E = B.schur E := by
  simp [centerResidual, schur, eta, div_eq_mul_inv, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, mul_comm, mul_left_comm, pow_two]

/--
With nonzero denominator, the transverse equations are solved by
`eta_i = -b_i/(lambda_i-E)`.
-/
theorem transverseResidual_eq_zero (B : DiagonalSchurBlock ι) {E : ℝ} (i : ι)
    (hden : B.transverse i - E ≠ 0) :
    B.transverseResidual E i = 0 := by
  unfold transverseResidual eta
  field_simp [hden]
  ring

/-- A Schur root below the transverse block supplies the finite eigen-equations. -/
theorem eigenEquations_of_schur_eq_zero (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) (hschur : B.schur E = 0) :
    B.centerResidual E = 0 ∧ ∀ i : ι, B.transverseResidual E i = 0 := by
  constructor
  · rw [B.centerResidual_eq_schur]
    exact hschur
  · intro i
    exact B.transverseResidual_eq_zero i (B.denom_ne_of_below hbelow i)

/-- The center equation alone recovers the Schur root equation. -/
theorem schur_eq_zero_of_centerResidual_eq_zero (B : DiagonalSchurBlock ι)
    {E : ℝ} (hcenter : B.centerResidual E = 0) :
    B.schur E = 0 := by
  rw [← B.centerResidual_eq_schur]
  exact hcenter

/--
Below the transverse block, the Schur root equation is equivalent to the finite
block eigen-equations for the vector with line component `1`.
-/
theorem eigenEquations_iff_schur_eq_zero (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) :
    (B.centerResidual E = 0 ∧ ∀ i : ι, B.transverseResidual E i = 0) ↔
      B.schur E = 0 := by
  constructor
  · intro h
    exact B.schur_eq_zero_of_centerResidual_eq_zero h.1
  · intro h
    exact B.eigenEquations_of_schur_eq_zero hbelow h

/-- The squared transverse-to-line size of the constructed eigenvector. -/
noncomputable def transverseRatioSq (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  ∑ i : ι, (B.eta E i) ^ 2

/-- The constructed transverse ratio square is nonnegative. -/
theorem transverseRatioSq_nonnegative (B : DiagonalSchurBlock ι) (E : ℝ) :
    0 <= B.transverseRatioSq E := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared line mass after normalizing the vector with line component `1`. -/
noncomputable def normalizedLineMassSq (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  1 / (1 + B.transverseRatioSq E)

/--
Squared transverse mass after normalizing the vector with line component `1`.
-/
noncomputable def normalizedTransverseMassSq (B : DiagonalSchurBlock ι)
    (E : ℝ) : ℝ :=
  B.transverseRatioSq E / (1 + B.transverseRatioSq E)

/-- The normalization denominator `1 + ||eta||^2` is positive. -/
theorem normalizedDenominator_pos (B : DiagonalSchurBlock ι) (E : ℝ) :
    0 < 1 + B.transverseRatioSq E := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (B.transverseRatioSq_nonnegative E)

/-- The normalized line mass is positive. -/
theorem normalizedLineMassSq_pos (B : DiagonalSchurBlock ι) (E : ℝ) :
    0 < B.normalizedLineMassSq E := by
  exact div_pos zero_lt_one (B.normalizedDenominator_pos E)

/-- The normalized transverse mass is nonnegative. -/
theorem normalizedTransverseMassSq_nonnegative (B : DiagonalSchurBlock ι)
    (E : ℝ) :
    0 <= B.normalizedTransverseMassSq E := by
  exact div_nonneg (B.transverseRatioSq_nonnegative E)
    (le_of_lt (B.normalizedDenominator_pos E))

/-- The normalized line and transverse squared masses sum to `1`. -/
theorem normalizedMassSq_sum_eq_one (B : DiagonalSchurBlock ι) (E : ℝ) :
    B.normalizedLineMassSq E + B.normalizedTransverseMassSq E = 1 := by
  have hden : 1 + B.transverseRatioSq E ≠ 0 :=
    ne_of_gt (B.normalizedDenominator_pos E)
  unfold normalizedLineMassSq normalizedTransverseMassSq
  field_simp [hden]

/--
The normalized transverse mass is bounded by the raw transverse-to-line squared
ratio.
-/
theorem normalizedTransverseMassSq_le_ratioSq (B : DiagonalSchurBlock ι)
    (E : ℝ) :
    B.normalizedTransverseMassSq E <= B.transverseRatioSq E := by
  have hnon : 0 <= B.transverseRatioSq E := B.transverseRatioSq_nonnegative E
  have hden_pos : 0 < 1 + B.transverseRatioSq E := B.normalizedDenominator_pos E
  unfold normalizedTransverseMassSq
  rw [div_le_iff₀ hden_pos]
  nlinarith [hnon]

/-- The normalized line mass is one minus the normalized transverse mass. -/
theorem normalizedLineMassSq_eq_one_sub_transverseMassSq
    (B : DiagonalSchurBlock ι) (E : ℝ) :
    B.normalizedLineMassSq E = 1 - B.normalizedTransverseMassSq E := by
  linarith [B.normalizedMassSq_sum_eq_one E]

/--
A bound on the raw transverse-to-line squared ratio bounds the normalized
transverse mass.
-/
theorem normalizedTransverseMassSq_le_of_ratioSq_le
    (B : DiagonalSchurBlock ι) (E eps : ℝ)
    (h : B.transverseRatioSq E <= eps) :
    B.normalizedTransverseMassSq E <= eps :=
  le_trans (B.normalizedTransverseMassSq_le_ratioSq E) h

/--
A bound on the raw transverse-to-line squared ratio gives the corresponding
lower bound on normalized line mass.
-/
theorem one_sub_eps_le_normalizedLineMassSq_of_ratioSq_le
    (B : DiagonalSchurBlock ι) (E eps : ℝ)
    (h : B.transverseRatioSq E <= eps) :
    1 - eps <= B.normalizedLineMassSq E := by
  have ht : B.normalizedTransverseMassSq E <= eps :=
    B.normalizedTransverseMassSq_le_of_ratioSq_le E eps h
  have hsum := B.normalizedMassSq_sum_eq_one E
  linarith

/--
Below the transverse block, each coupling denominator decreases as `E`
increases, so the corresponding positive coupling term increases.
-/
theorem couplingTerm_le_of_lt {B : DiagonalSchurBlock ι} {E1 E2 : ℝ} (i : ι)
    (h12 : E1 < E2) (hbelow2 : B.BelowTransverse E2) :
    (B.coupling i) ^ 2 / (B.transverse i - E1) ≤
      (B.coupling i) ^ 2 / (B.transverse i - E2) := by
  have hd2 : 0 < B.transverse i - E2 := sub_pos.mpr (hbelow2 i)
  have hle : B.transverse i - E2 ≤ B.transverse i - E1 := by
    exact le_of_lt (sub_lt_sub_left h12 (B.transverse i))
  exact div_le_div_of_nonneg_left (sq_nonneg (B.coupling i)) hd2 hle

/-- The full coupling sum is monotone increasing below the transverse block. -/
theorem couplingSum_le_of_lt {B : DiagonalSchurBlock ι} {E1 E2 : ℝ}
    (h12 : E1 < E2) (hbelow2 : B.BelowTransverse E2) :
    (∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E1)) ≤
      (∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E2)) := by
  exact Finset.sum_le_sum fun i _ => couplingTerm_le_of_lt i h12 hbelow2

/--
The finite Schur function is strictly decreasing below the transverse block.
This is the non-calculus form of
`Phi'(E) = -1 - sum_i b_i^2/(lambda_i-E)^2 < 0`.
-/
theorem schur_strictAnti_of_lt {B : DiagonalSchurBlock ι} {E1 E2 : ℝ}
    (h12 : E1 < E2) (hbelow2 : B.BelowTransverse E2) :
    B.schur E2 < B.schur E1 := by
  let s1 : ℝ := ∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E1)
  let s2 : ℝ := ∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E2)
  have hs : s1 ≤ s2 := by
    simpa [s1, s2] using B.couplingSum_le_of_lt h12 hbelow2
  have hbase : B.q - E2 < B.q - E1 := sub_lt_sub_left h12 B.q
  have hleft : B.q - E2 - s2 < B.q - E1 - s2 :=
    sub_lt_sub_right hbase s2
  have hright : B.q - E1 - s2 ≤ B.q - E1 - s1 :=
    sub_le_sub_left hs (B.q - E1)
  have hmain : B.q - E2 - s2 < B.q - E1 - s1 :=
    lt_of_lt_of_le hleft hright
  simpa [schur, s1, s2] using hmain

/-- A below-transverse Schur root is unique. -/
theorem schur_root_unique_of_below {B : DiagonalSchurBlock ι} {E1 E2 : ℝ}
    (hbelow1 : B.BelowTransverse E1) (hbelow2 : B.BelowTransverse E2)
    (hroot1 : B.schur E1 = 0) (hroot2 : B.schur E2 = 0) :
    E1 = E2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h12 | h21
  · have hlt := B.schur_strictAnti_of_lt h12 hbelow2
    rw [hroot1, hroot2] at hlt
    exact (lt_irrefl (0 : ℝ)) hlt
  · have hlt := B.schur_strictAnti_of_lt h21 hbelow1
    rw [hroot1, hroot2] at hlt
    exact (lt_irrefl (0 : ℝ)) hlt

section DeterminantFactor

variable [DecidableEq ι]

/-- Product of the transverse Schur denominators. -/
noncomputable def transverseProduct (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  ∏ i : ι, (B.transverse i - E)

/-- Product of all transverse denominators except the `i`-th one. -/
noncomputable def transverseMinorProduct (B : DiagonalSchurBlock ι) (E : ℝ)
    (i : ι) : ℝ :=
  (Finset.univ.erase i).prod (fun j : ι => B.transverse j - E)

/--
The expanded diagonal-transverse determinant numerator obtained by clearing
the Schur denominators.
-/
noncomputable def expandedDeterminant (B : DiagonalSchurBlock ι) (E : ℝ) : ℝ :=
  (B.q - E) * B.transverseProduct E -
    ∑ i : ι, (B.coupling i) ^ 2 * B.transverseMinorProduct E i

/-- The transverse product splits into one denominator times its minor product. -/
lemma transverseProduct_eq_den_mul_minor (B : DiagonalSchurBlock ι) (E : ℝ)
    (i : ι) :
    B.transverseProduct E =
      (B.transverse i - E) * B.transverseMinorProduct E i := by
  classical
  simpa [transverseProduct, transverseMinorProduct] using
    (Finset.mul_prod_erase (Finset.univ) (fun j : ι => B.transverse j - E)
      (Finset.mem_univ i)).symm

/--
Clearing a single Schur denominator gives the corresponding transverse minor
term.
-/
lemma transverseProduct_mul_div_eq_minor (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) (i : ι) :
    B.transverseProduct E * ((B.coupling i) ^ 2 / (B.transverse i - E)) =
      (B.coupling i) ^ 2 * B.transverseMinorProduct E i := by
  classical
  have hden : B.transverse i - E ≠ 0 := B.denom_ne_of_below hbelow i
  rw [B.transverseProduct_eq_den_mul_minor E i]
  field_simp [hden]

/--
Clearing all Schur denominators gives the expanded finite determinant
numerator.

This is the diagonal-transverse form of
`det(Q-EI)=det(C-EI)*Phi(E)`.
-/
theorem transverseProduct_mul_schur_eq_expandedDeterminant
    (B : DiagonalSchurBlock ι) {E : ℝ} (hbelow : B.BelowTransverse E) :
    B.transverseProduct E * B.schur E = B.expandedDeterminant E := by
  classical
  calc
    B.transverseProduct E * B.schur E
        = B.transverseProduct E * (B.q - E) -
            B.transverseProduct E *
              (∑ i : ι, (B.coupling i) ^ 2 / (B.transverse i - E)) := by
            simp [schur]
            ring
    _ = B.transverseProduct E * (B.q - E) -
            ∑ i : ι, B.transverseProduct E *
              ((B.coupling i) ^ 2 / (B.transverse i - E)) := by
            rw [Finset.mul_sum]
    _ = B.transverseProduct E * (B.q - E) -
            ∑ i : ι, (B.coupling i) ^ 2 * B.transverseMinorProduct E i := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            exact B.transverseProduct_mul_div_eq_minor hbelow i
    _ = B.expandedDeterminant E := by
            simp [expandedDeterminant]
            ring

omit [DecidableEq ι] in
/-- The transverse denominator product is positive below the transverse block. -/
theorem transverseProduct_pos_of_below (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) :
    0 < B.transverseProduct E := by
  classical
  unfold transverseProduct
  exact Finset.prod_pos fun i _ => sub_pos.mpr (hbelow i)

omit [DecidableEq ι] in
/-- The transverse denominator product is nonzero below the transverse block. -/
theorem transverseProduct_ne_zero_of_below (B : DiagonalSchurBlock ι) {E : ℝ}
    (hbelow : B.BelowTransverse E) :
    B.transverseProduct E ≠ 0 :=
  ne_of_gt (B.transverseProduct_pos_of_below hbelow)

/--
Below the transverse block, zeros of the cleared determinant numerator are
exactly Schur roots.
-/
theorem expandedDeterminant_eq_zero_iff_schur_eq_zero
    (B : DiagonalSchurBlock ι) {E : ℝ} (hbelow : B.BelowTransverse E) :
    B.expandedDeterminant E = 0 ↔ B.schur E = 0 := by
  constructor
  · intro hdet
    have hmul : B.transverseProduct E * B.schur E = 0 := by
      rw [B.transverseProduct_mul_schur_eq_expandedDeterminant hbelow]
      exact hdet
    rcases mul_eq_zero.mp hmul with hp | hs
    · exact False.elim ((B.transverseProduct_ne_zero_of_below hbelow) hp)
    · exact hs
  · intro hschur
    rw [← B.transverseProduct_mul_schur_eq_expandedDeterminant hbelow,
      hschur, mul_zero]

/--
Below the transverse block, the cleared determinant numerator and the Schur
function have the same positive sign.
-/
theorem expandedDeterminant_pos_iff_schur_pos_of_below
    (B : DiagonalSchurBlock ι) {E : ℝ} (hbelow : B.BelowTransverse E) :
    0 < B.expandedDeterminant E ↔ 0 < B.schur E := by
  have hprod : 0 < B.transverseProduct E :=
    B.transverseProduct_pos_of_below hbelow
  have hdet := B.transverseProduct_mul_schur_eq_expandedDeterminant hbelow
  constructor
  · intro hpos
    rw [← hdet] at hpos
    nlinarith
  · intro hschur
    rw [← hdet]
    nlinarith

/--
Below the transverse block, the cleared determinant numerator and the Schur
function have the same nonnegative sign.
-/
theorem expandedDeterminant_nonneg_iff_schur_nonneg_of_below
    (B : DiagonalSchurBlock ι) {E : ℝ} (hbelow : B.BelowTransverse E) :
    0 <= B.expandedDeterminant E ↔ 0 <= B.schur E := by
  have hprod : 0 < B.transverseProduct E :=
    B.transverseProduct_pos_of_below hbelow
  have hdet := B.transverseProduct_mul_schur_eq_expandedDeterminant hbelow
  constructor
  · intro hnonneg
    rw [← hdet] at hnonneg
    nlinarith
  · intro hschur
    rw [← hdet]
    nlinarith

/--
Below the transverse block, zeros of the cleared determinant numerator are
exactly the block eigen-equations for the vector with line component `1`.
-/
theorem expandedDeterminant_eq_zero_iff_eigenEquations
    (B : DiagonalSchurBlock ι) {E : ℝ} (hbelow : B.BelowTransverse E) :
    B.expandedDeterminant E = 0 ↔
      (B.centerResidual E = 0 ∧ ∀ i : ι, B.transverseResidual E i = 0) := by
  constructor
  · intro hdet
    have hschur : B.schur E = 0 :=
      (B.expandedDeterminant_eq_zero_iff_schur_eq_zero hbelow).1 hdet
    exact (B.eigenEquations_iff_schur_eq_zero hbelow).2 hschur
  · intro heig
    have hschur : B.schur E = 0 :=
      (B.eigenEquations_iff_schur_eq_zero hbelow).1 heig
    exact (B.expandedDeterminant_eq_zero_iff_schur_eq_zero hbelow).2 hschur

/-- A below-transverse zero of the cleared determinant numerator is unique. -/
theorem expandedDeterminant_root_unique_of_below
    {B : DiagonalSchurBlock ι} {E1 E2 : ℝ}
    (hbelow1 : B.BelowTransverse E1) (hbelow2 : B.BelowTransverse E2)
    (hroot1 : B.expandedDeterminant E1 = 0)
    (hroot2 : B.expandedDeterminant E2 = 0) :
    E1 = E2 :=
  B.schur_root_unique_of_below hbelow1 hbelow2
    ((B.expandedDeterminant_eq_zero_iff_schur_eq_zero hbelow1).1 hroot1)
    ((B.expandedDeterminant_eq_zero_iff_schur_eq_zero hbelow2).1 hroot2)

/--
Below the transverse block, a cleared determinant zero plus a raw response
bound gives both the finite block eigen-equations and normalized line control.
-/
theorem determinantZero_eigenEquations_and_lineControl_of_ratioSq_le
    (B : DiagonalSchurBlock ι) {E eps : ℝ}
    (hbelow : B.BelowTransverse E)
    (hdet : B.expandedDeterminant E = 0)
    (hratio : B.transverseRatioSq E <= eps) :
    (B.centerResidual E = 0 ∧ ∀ i : ι, B.transverseResidual E i = 0) ∧
      B.normalizedTransverseMassSq E <= eps ∧
      1 - eps <= B.normalizedLineMassSq E := by
  exact ⟨(B.expandedDeterminant_eq_zero_iff_eigenEquations hbelow).1 hdet,
    B.normalizedTransverseMassSq_le_of_ratioSq_le E eps hratio,
    B.one_sub_eps_le_normalizedLineMassSq_of_ratioSq_le E eps hratio⟩

end DeterminantFactor

end DiagonalSchurBlock

end ResidualSchurSelector
end JensenLadder
