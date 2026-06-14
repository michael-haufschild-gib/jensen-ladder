import JensenLadder.DHMultiplicityFakeGate

/-!
# Finite Euler-product mixed-log gate

This file formalizes the finite algebra behind the first mixed
Euler-product/log-derivative fake gate.

For a local two-variable Dirichlet coefficient block

`1 + a_m x + a_n y + a_mn x*y`,

the mixed `x*y` coefficient of the formal logarithm is `a_mn - a_m*a_n`.
Thus mixed log cancellation is exactly the finite product relation
`a_mn = a_m*a_n`.

This is not an RH proof and not a global domination theorem.  It only names the
finite algebraic row where a single Euler product differs from DH-style
nonmultiplicative replays.

Evidence class: proved finite algebra lemma.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace FiniteEulerProductMixedLogGate

open DHMultiplicityFakeGate

/--
The mixed `xy` coefficient in
`log(1 + am*x + an*y + amn*x*y)`.
-/
def mixedLogCoeff (am an amn : ℝ) : ℝ :=
  amn - am * an

/-- The mixed log coefficient at a finite pair of coefficient indices. -/
def mixedLogCoeffOf (a : ℕ -> ℝ) (m n : ℕ) : ℝ :=
  mixedLogCoeff (a m) (a n) (a (m * n))

/-- Mixed log cancellation is exactly the finite product relation. -/
theorem mixedLogCoeff_eq_zero_iff_product_relation
    {am an amn : ℝ} :
    mixedLogCoeff am an amn = 0 ↔ amn = am * an := by
  unfold mixedLogCoeff
  constructor <;> intro h <;> linarith

/-- Stream version of `mixedLogCoeff_eq_zero_iff_product_relation`. -/
theorem mixedLogCoeffOf_eq_zero_iff_product_relation
    {a : ℕ -> ℝ} {m n : ℕ} :
    mixedLogCoeffOf a m n = 0 ↔ a (m * n) = a m * a n := by
  unfold mixedLogCoeffOf
  exact mixedLogCoeff_eq_zero_iff_product_relation

/-- The zeta unit coefficient stream has zero mixed log coefficient at every
pair. -/
theorem zetaUnit_mixedLogCoeffOf_eq_zero
    (m n : ℕ) :
    mixedLogCoeffOf (fun _ : ℕ => (1 : ℝ)) m n = 0 := by
  rw [mixedLogCoeffOf_eq_zero_iff_product_relation]
  simp

/-- The DH `(2,3,6)` finite pattern has mixed log coefficient `1 + kappa^2`. -/
theorem dhPattern236_mixedLogCoeffOf_eq_one_add_sq
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    mixedLogCoeffOf a 2 3 = 1 + kappa ^ 2 := by
  rcases h with ⟨_h1, h2, h3, h6⟩
  unfold mixedLogCoeffOf mixedLogCoeff
  norm_num
  rw [h6, h2, h3]
  ring

/-- The DH `(2,3,6)` mixed log coefficient is strictly positive. -/
theorem dhPattern236_mixedLogCoeffOf_pos
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    0 < mixedLogCoeffOf a 2 3 := by
  rw [dhPattern236_mixedLogCoeffOf_eq_one_add_sq h]
  nlinarith [sq_nonneg kappa]

/-- The DH `(2,3,6)` finite pattern fails mixed log cancellation. -/
theorem dhPattern236_mixedLogCoeffOf_ne_zero
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    mixedLogCoeffOf a 2 3 ≠ 0 :=
  ne_of_gt (dhPattern236_mixedLogCoeffOf_pos h)

end FiniteEulerProductMixedLogGate
end JensenLadder

namespace JensenLadder
namespace FiniteEulerProductMixedLogGate

open DHMultiplicityFakeGate

/-- A finite packet of mixed log cancellations. -/
def MixedLogCancellationOn (R : Finset (ℕ × ℕ)) (a : ℕ -> ℝ) : Prop :=
  ∀ mn : ℕ × ℕ, mn ∈ R -> mixedLogCoeffOf a mn.1 mn.2 = 0

/-- The matching finite packet of product relations. -/
def ProductRelationsOn (R : Finset (ℕ × ℕ)) (a : ℕ -> ℝ) : Prop :=
  ∀ mn : ℕ × ℕ, mn ∈ R -> a (mn.1 * mn.2) = a mn.1 * a mn.2

/-- Packet-level mixed log cancellation is exactly packet-level product multiplicativity. -/
theorem mixedLogCancellationOn_iff_productRelationsOn
    {R : Finset (ℕ × ℕ)} {a : ℕ -> ℝ} :
    MixedLogCancellationOn R a ↔ ProductRelationsOn R a := by
  constructor
  · intro h mn hmn
    exact (mixedLogCoeffOf_eq_zero_iff_product_relation
      (a := a) (m := mn.1) (n := mn.2)).1 (h mn hmn)
  · intro h mn hmn
    exact (mixedLogCoeffOf_eq_zero_iff_product_relation
      (a := a) (m := mn.1) (n := mn.2)).2 (h mn hmn)

/-- The zeta unit coefficient stream satisfies every finite mixed-log packet. -/
theorem zetaUnit_mixedLogCancellationOn
    (R : Finset (ℕ × ℕ)) :
    MixedLogCancellationOn R (fun _ : ℕ => (1 : ℝ)) := by
  intro mn _hmn
  exact zetaUnit_mixedLogCoeffOf_eq_zero mn.1 mn.2

/-- At `(2,3)`, mixed log cancellation is exactly `a_6 = a_2*a_3`. -/
theorem mixedLogCoeffOf_pair23_eq_zero_iff_product236
    {a : ℕ -> ℝ} :
    mixedLogCoeffOf a 2 3 = 0 ↔ a 6 = a 2 * a 3 := by
  rw [mixedLogCoeffOf_eq_zero_iff_product_relation]

/-- Any finite mixed-log packet containing `(2,3)` rejects the DH finite pattern. -/
theorem dhPattern236_not_mixedLogCancellationOn_of_pair23_mem
    {R : Finset (ℕ × ℕ)} {a : ℕ -> ℝ} {kappa : ℝ}
    (hR : ((2, 3) : ℕ × ℕ) ∈ R)
    (h : DHPattern236 a kappa) :
    ¬ MixedLogCancellationOn R a := by
  intro hcancel
  have hzero : mixedLogCoeffOf a 2 3 = 0 := hcancel ((2, 3) : ℕ × ℕ) hR
  exact dhPattern236_mixedLogCoeffOf_ne_zero h hzero

/-- The singleton packet containing only `(2,3)` already rejects DH. -/
theorem dhPattern236_not_mixedLogCancellationOn_singleton23
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    ¬ MixedLogCancellationOn {((2, 3) : ℕ × ℕ)} a := by
  exact dhPattern236_not_mixedLogCancellationOn_of_pair23_mem (by simp) h

end FiniteEulerProductMixedLogGate
end JensenLadder

namespace JensenLadder
namespace FiniteEulerProductMixedLogGate

open DHMultiplicityFakeGate

/-- The log row has no mixed term at any coprime pair. -/
def CoprimeMixedLogFree (a : ℕ -> ℝ) : Prop :=
  ∀ m n : ℕ, Nat.Coprime m n -> mixedLogCoeffOf a m n = 0

/-- Coprime mixed-log freeness is exactly coprime multiplicativity. -/
theorem coprimeMixedLogFree_iff_coprimeMultiplicative
    {a : ℕ -> ℝ} :
    CoprimeMixedLogFree a ↔ CoprimeMultiplicative a := by
  constructor
  · intro hfree m n hcop
    exact (mixedLogCoeffOf_eq_zero_iff_product_relation
      (a := a) (m := m) (n := n)).1 (hfree m n hcop)
  · intro hmul m n hcop
    exact (mixedLogCoeffOf_eq_zero_iff_product_relation
      (a := a) (m := m) (n := n)).2 (hmul m n hcop)

/-- The zeta unit coefficient stream has no mixed log term at any coprime pair. -/
theorem zetaUnit_coprimeMixedLogFree :
    CoprimeMixedLogFree (fun _ : ℕ => (1 : ℝ)) := by
  rw [coprimeMixedLogFree_iff_coprimeMultiplicative]
  exact zetaUnit_coprimeMultiplicative

/-- A coprime-mixed-log-free stream satisfies every finite packet of coprime rows. -/
theorem mixedLogCancellationOn_of_coprimeMixedLogFree
    {R : Finset (ℕ × ℕ)} {a : ℕ -> ℝ}
    (hfree : CoprimeMixedLogFree a)
    (hcopR : ∀ mn : ℕ × ℕ, mn ∈ R -> Nat.Coprime mn.1 mn.2) :
    MixedLogCancellationOn R a := by
  intro mn hmn
  exact hfree mn.1 mn.2 (hcopR mn hmn)

/-- The DH `(2,3,6)` pattern is not coprime mixed-log free. -/
theorem dhPattern236_not_coprimeMixedLogFree
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    ¬ CoprimeMixedLogFree a := by
  rw [coprimeMixedLogFree_iff_coprimeMultiplicative]
  exact not_coprimeMultiplicative_of_DHPattern236 h

/-- Failure of the global coprime mixed-log row is already witnessed at `(2,3)`. -/
theorem exists_coprime_pair_mixedLogCoeffOf_ne_zero_of_DHPattern236
    {a : ℕ -> ℝ} {kappa : ℝ}
    (h : DHPattern236 a kappa) :
    ∃ m n : ℕ, Nat.Coprime m n ∧ mixedLogCoeffOf a m n ≠ 0 := by
  exact ⟨2, 3, by decide, dhPattern236_mixedLogCoeffOf_ne_zero h⟩

end FiniteEulerProductMixedLogGate
end JensenLadder
