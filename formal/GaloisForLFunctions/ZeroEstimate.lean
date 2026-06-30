import GaloisForLFunctions.Core

open scoped BigOperators

/-!
# Uniform zero-estimate height bound (Tier A)

This file formalizes the elementary height inequality from
`docs/drafts/pipeline/2-fully-proven/zero-estimate-uniformity.md`.

For a finitely supported integer exponent vector `m`, the prime-log frequency
`Σ_p m_p log p` is `log(a/b)`, where `a` and `b` are the positive and negative
prime products. If `m ≠ 0`, unique factorization gives `a ≠ b`, and the
elementary inequality `log(a/b) ≥ 1/(ab)` (after ordering `a,b`) gives an
S-free lower bound in terms of the height `H(m)=ab`.

The analytic Vandermonde order bound for exponential sums is not formalized
here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Multiplicative height of a finite integer prime-exponent vector:
`H(m)=∏ p^{|m_p|}`. -/
def primeLogHeight (m : Nat.Primes →₀ ℤ) : ℕ :=
  primeProduct (positivePart m) * primeProduct (negativePart m)

lemma primeLogHeight_pos (m : Nat.Primes →₀ ℤ) : 0 < primeLogHeight m := by
  exact mul_pos (primeProduct_pos _) (primeProduct_pos _)

private lemma one_sub_inv_le_log {x : ℝ} (hx : 1 ≤ x) : 1 - x⁻¹ ≤ Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hposinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have h := Real.log_le_sub_one_of_pos hposinv
  rw [Real.log_inv] at h
  linarith

private lemma inv_mul_le_one_sub_div_inv {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (((a * b : ℕ) : ℝ))⁻¹ ≤ 1 - (((a : ℝ) / (b : ℝ))⁻¹) := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hb1 : 1 ≤ (b : ℝ) := by
    have hbNat : 1 ≤ b := Nat.succ_le_iff.mpr hb
    exact_mod_cast hbNat
  have hdiff : 1 ≤ (a : ℝ) - (b : ℝ) := by
    have hnat : b + 1 ≤ a := Nat.succ_le_of_lt hba
    have hnatR : ((b + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hnat
    norm_num at hnatR ⊢
    linarith
  rw [Nat.cast_mul]
  field_simp [haR.ne', hbR.ne']
  have hmul : (1 : ℝ) ≤ (b : ℝ) * ((a : ℝ) - (b : ℝ)) := by
    nlinarith [mul_le_mul hb1 hdiff (by linarith) (by linarith)]
  nlinarith

private lemma log_ratio_height_bound {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (((a * b : ℕ) : ℝ))⁻¹ ≤ Real.log (a : ℝ) - Real.log (b : ℝ) := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hle : 1 ≤ (a : ℝ) / (b : ℝ) := by
    rw [one_le_div hbR]
    exact_mod_cast le_of_lt hba
  have hlog := one_sub_inv_le_log hle
  have hinv := inv_mul_le_one_sub_div_inv ha hb hba
  have hlogdiv : Real.log ((a : ℝ) / (b : ℝ)) = Real.log (a : ℝ) - Real.log (b : ℝ) := by
    rw [Real.log_div haR.ne' hbR.ne']
  rw [hlogdiv] at hlog
  exact le_trans hinv hlog

lemma logPrime_int_sum_eq_log_pos_sub_log_neg (m : Nat.Primes →₀ ℤ) :
    m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ)) =
      Real.log (primeProduct (positivePart m) : ℝ) -
        Real.log (primeProduct (negativePart m) : ℝ) := by
  let fNat : Nat.Primes → ℕ → ℝ := fun p k => (k : ℝ) * Real.log (p : ℕ)
  let fInt : Nat.Primes → ℤ → ℝ := fun p z => (z : ℝ) * Real.log (p : ℕ)
  have hdiff :
      (positivePart m).sum fNat - (negativePart m).sum fNat = m.sum fInt := by
    calc
      (positivePart m).sum fNat - (negativePart m).sum fNat
          = (positivePartZ m).sum fInt - (negativePartZ m).sum fInt := by
              rw [positivePartZ_sum, negativePartZ_sum]
      _ = (positivePartZ m - negativePartZ m).sum fInt := by
              rw [Finsupp.sum_sub_index]
              intro _ _ _
              simp [fInt, sub_mul]
      _ = m.sum fInt := by
              rw [positivePartZ_sub_negativePartZ]
  rw [log_primeProduct, log_primeProduct]
  exact hdiff.symm

lemma positive_negative_eq_zero_of_primeProduct_eq {m : Nat.Primes →₀ ℤ}
    (h : primeProduct (positivePart m) = primeProduct (negativePart m)) :
    m = 0 := by
  have hparts : positivePart m = negativePart m := primeProduct_injective h
  ext p
  have hp : positivePart m p = negativePart m p := congrArg (fun f => f p) hparts
  have hpz : ((m p).toNat : ℤ) = ((-(m p)).toNat : ℤ) := by
    exact_mod_cast hp
  have hsub : ((m p).toNat : ℤ) - ((-(m p)).toNat : ℤ) = 0 := sub_eq_zero.mpr hpz
  rwa [int_toNat_sub_neg_toNat] at hsub

/-- **S-free height bound for prime logarithm frequencies.** For every nonzero
finite integer exponent vector `m`,
`H(m)⁻¹ ≤ |Σ_p m_p log p|`, where `H(m)=∏ p^{|m_p|}`. -/
theorem logPrime_height_bound (m : Nat.Primes →₀ ℤ) (hm : m ≠ 0) :
    ((primeLogHeight m : ℝ))⁻¹ ≤
      |m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ))| := by
  let a := primeProduct (positivePart m)
  let b := primeProduct (negativePart m)
  have ha : 0 < a := primeProduct_pos _
  have hb : 0 < b := primeProduct_pos _
  have habne : a ≠ b := by
    intro h
    exact hm (positive_negative_eq_zero_of_primeProduct_eq h)
  have hsum := logPrime_int_sum_eq_log_pos_sub_log_neg m
  change m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ)) =
      Real.log (a : ℝ) - Real.log (b : ℝ) at hsum
  rcases lt_or_gt_of_ne habne with hab | hba
  · have hbound := log_ratio_height_bound hb ha hab
    have hnonneg : 0 ≤ Real.log (b : ℝ) - Real.log (a : ℝ) := by
      have hpos : 0 < (((b * a : ℕ) : ℝ))⁻¹ := by
        exact inv_pos.mpr (Nat.cast_pos.mpr (mul_pos hb ha))
      exact le_trans hpos.le hbound
    have hnonpos : Real.log (a : ℝ) - Real.log (b : ℝ) ≤ 0 := by linarith
    calc
      ((primeLogHeight m : ℝ))⁻¹ = (((b * a : ℕ) : ℝ))⁻¹ := by
        simp [primeLogHeight, a, b, Nat.mul_comm]
      _ ≤ Real.log (b : ℝ) - Real.log (a : ℝ) := hbound
      _ = |m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ))| := by
        rw [hsum, abs_of_nonpos hnonpos]
        ring
  · have hbound := log_ratio_height_bound ha hb hba
    have hnonneg : 0 ≤ Real.log (a : ℝ) - Real.log (b : ℝ) := by
      have hpos : 0 < (((a * b : ℕ) : ℝ))⁻¹ := by
        exact inv_pos.mpr (Nat.cast_pos.mpr (mul_pos ha hb))
      exact le_trans hpos.le hbound
    calc
      ((primeLogHeight m : ℝ))⁻¹ = (((a * b : ℕ) : ℝ))⁻¹ := by
        simp [primeLogHeight, a, b]
      _ ≤ Real.log (a : ℝ) - Real.log (b : ℝ) := hbound
      _ = |m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ))| := by
        rw [hsum, abs_of_nonneg hnonneg]

/-- If the first `n` power moments of a coefficient vector vanish, then it also
pairs to zero against every polynomial of degree `< n`. -/
private lemma weighted_eval_eq_zero_of_moments {n : ℕ} {μ c : Fin n → ℂ} {p : Polynomial ℂ}
    (hp : p.natDegree < n)
    (hmom : ∀ k : Fin n, ∑ j : Fin n, c j * (μ j) ^ (k : ℕ) = 0) :
    ∑ j : Fin n, c j * p.eval (μ j) = 0 := by
  calc
    ∑ j : Fin n, c j * p.eval (μ j)
        = ∑ j : Fin n, c j *
            (∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (μ j) ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Polynomial.eval_eq_sum_range]
    _ = ∑ j : Fin n, ∑ k ∈ Finset.range (p.natDegree + 1),
          c j * (p.coeff k * (μ j) ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (p.natDegree + 1), ∑ j : Fin n,
          c j * (p.coeff k * (μ j) ^ k) := by
            rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          p.coeff k * (∑ j : Fin n, c j * (μ j) ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
    _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro k hk
            have hklt : k < n := by
              have hk' : k < p.natDegree + 1 := Finset.mem_range.mp hk
              omega
            have h := hmom ⟨k, hklt⟩
            rw [h, mul_zero]

/-- The Lagrange numerator that vanishes at every node except `i`. -/
private def lagrangeComplement {n : ℕ} (μ : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  (Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (μ j))

private lemma lagrangeComplement_natDegree_lt {n : ℕ} (μ : Fin n → ℂ) (i : Fin n) :
    (lagrangeComplement μ i).natDegree < n := by
  unfold lagrangeComplement
  have hle₁ : ((Finset.univ.erase i).prod
      (fun j => Polynomial.X - Polynomial.C (μ j))).natDegree ≤
      ∑ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (μ j) : Polynomial ℂ).natDegree :=
    Polynomial.natDegree_prod_le _ _
  have hle₂ :
      (∑ j ∈ Finset.univ.erase i,
          (Polynomial.X - Polynomial.C (μ j) : Polynomial ℂ).natDegree) ≤
        (Finset.univ.erase i).card := by
    simp
  have hcard : (Finset.univ.erase i).card < n := by
    have hnpos : 0 < n := Fin.pos i
    rw [Finset.card_erase_of_mem]
    · simp
      omega
    · simp
  exact lt_of_le_of_lt (le_trans hle₁ hle₂) hcard

private lemma lagrangeComplement_eval_ne_zero {n : ℕ} {μ : Fin n → ℂ}
    (hμ : Function.Injective μ) (i : Fin n) :
    (lagrangeComplement μ i).eval (μ i) ≠ 0 := by
  unfold lagrangeComplement
  rw [Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  intro hsub
  have hij : i = j := hμ (sub_eq_zero.mp hsub)
  exact hji hij.symm

private lemma lagrangeComplement_eval_eq_zero_of_ne {n : ℕ} {μ : Fin n → ℂ}
    (i j : Fin n) (hji : j ≠ i) :
    (lagrangeComplement μ i).eval (μ j) = 0 := by
  unfold lagrangeComplement
  rw [Polynomial.eval_prod]
  rw [Finset.prod_eq_zero_iff]
  refine ⟨j, ?_, ?_⟩
  · simp [hji]
  · simp

/-- **Vandermonde algebraic core.** At `n` distinct nodes, the first `n`
power moments determine the coefficient vector. Equivalently, a coefficient
vector whose moments `∑ j, c_j μ_j^k` vanish for `k=0,…,n-1` is zero. -/
theorem vandermonde_moments_eq_zero_of_injective {n : ℕ} {μ c : Fin n → ℂ}
    (hμ : Function.Injective μ)
    (hmom : ∀ k : Fin n, ∑ j : Fin n, c j * (μ j) ^ (k : ℕ) = 0) :
    c = 0 := by
  funext i
  let p := lagrangeComplement μ i
  have hp : p.natDegree < n := lagrangeComplement_natDegree_lt μ i
  have hsum : ∑ j : Fin n, c j * p.eval (μ j) = 0 :=
    weighted_eval_eq_zero_of_moments hp hmom
  have hsingle : ∑ j : Fin n, c j * p.eval (μ j) = c i * p.eval (μ i) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [lagrangeComplement_eval_eq_zero_of_ne i j hji, mul_zero]
    · intro hi
      simp at hi
  have hmul : c i * p.eval (μ i) = 0 := by
    rw [← hsingle]
    exact hsum
  have hpne : p.eval (μ i) ≠ 0 := lagrangeComplement_eval_ne_zero hμ i
  exact (mul_eq_zero.mp hmul).resolve_right hpne

/-- Direct order-bound form of the Vandermonde core: a nonzero coefficient
vector at distinct nodes has a nonzero moment among the first `n` moments. -/
theorem vandermonde_initial_moment_nonzero_of_nonzero_coeff {n : ℕ} {μ c : Fin n → ℂ}
    (hμ : Function.Injective μ) (hc : c ≠ 0) :
    ∃ k : Fin n, ∑ j : Fin n, c j * (μ j) ^ (k : ℕ) ≠ 0 := by
  by_contra hnone
  apply hc
  exact vandermonde_moments_eq_zero_of_injective hμ fun k => by
    exact not_not.mp (not_exists.mp hnone k)

end

end GaloisForLFunctions
