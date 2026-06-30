import Mathlib

/-!
# Infinite-base difference Galois for L-functions: Tier A core

This file formalizes the elementary Tier A facts from
`docs/drafts/infinite-base-difference-galois-for-L-functions.md`.
It deliberately contains no axioms or placeholders for the conjectural
difference-Galois field, RH, LI, or the boundary/archimedean program.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The functional-equation involution on the `s`-plane. -/
def sigma (s : ℂ) : ℂ := 1 - s

@[simp] theorem sigma_apply (s : ℂ) : sigma s = 1 - s := rfl

/-- The involution `s ↦ 1 - s` has order two. -/
theorem sigma_involutive (s : ℂ) : sigma (sigma s) = s := by
  simp [sigma]

/-- In Bohr coordinates, `s ↦ 1-s` is inversion and scale at every positive base. -/
theorem cpow_inversion_scale (p : ℝ) (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ (-(1 - s)) = (p : ℂ) ^ (-(1 : ℂ)) * (((p : ℂ) ^ (-s))⁻¹) := by
  have hpC : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [show -(1 - s) = s - 1 by ring]
  rw [Complex.cpow_sub s 1 hpC]
  rw [Complex.cpow_neg, Complex.cpow_neg]
  simp [div_eq_mul_inv, mul_comm]

/-- Absolute value of a positive real base raised to a complex exponent. -/
theorem norm_cpow_neg_eq_rpow_re (p : ℝ) (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = p ^ (-(s.re)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp (-s)]
  simp

/-- A single base `p > 1` detects the critical line as the fixed-modulus locus. -/
theorem norm_cpow_eq_critical_iff (p : ℝ) (hp : 1 < p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = p ^ (-(1 / 2 : ℝ)) ↔ s.re = 1 / 2 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  rw [norm_cpow_neg_eq_rpow_re p hp0 s]
  rw [Real.rpow_right_inj hp0 (ne_of_gt hp)]
  constructor <;> intro h <;> linarith

/-- The local Euler factor for zeta in one Bohr coordinate. -/
def localEulerFactor (x : ℂ) : ℂ := (1 - x)⁻¹

lemma localEulerFactor_relation {x : ℂ} (hx : x ≠ 1) :
    (1 - x) * localEulerFactor x = 1 := by
  unfold localEulerFactor
  have h : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  exact mul_inv_cancel₀ h

/-- The local Euler factor has no zeros away from its pole at `x = 1`. -/
lemma localEulerFactor_ne_zero {x : ℂ} (hx : x ≠ 1) :
    localEulerFactor x ≠ 0 := by
  unfold localEulerFactor
  exact inv_ne_zero (sub_ne_zero.mpr hx.symm)

/-- A finite Euler product of local zeta factors. -/
def finiteEulerProduct (S : Finset Nat.Primes) (x : Nat.Primes → ℂ) : ℂ :=
  ∏ p ∈ S, localEulerFactor (x p)

/-- Finite Euler products are zero-free where none of their local factors has a pole. -/
theorem finiteEulerProduct_ne_zero (S : Finset Nat.Primes) (x : Nat.Primes → ℂ)
    (hx : ∀ p ∈ S, x p ≠ 1) : finiteEulerProduct S x ≠ 0 := by
  classical
  unfold finiteEulerProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact localEulerFactor_ne_zero (hx p hp)

/-- Finite prime products from exponent vectors on `Nat.Primes`. -/
def primeProduct (m : Nat.Primes →₀ ℕ) : ℕ :=
  m.prod fun p k => (p : ℕ) ^ k

lemma primeProduct_factorization (m : Nat.Primes →₀ ℕ) (p : Nat.Primes) :
    (primeProduct m).factorization (p : ℕ) = m p := by
  classical
  unfold primeProduct
  rw [Finsupp.prod]
  rw [Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single p]
    · simp [p.2.factorization_self]
    · intro q _ hqp
      have hzero : (q : ℕ).factorization (p : ℕ) = 0 := by
        by_contra hne
        have hnat : (q : ℕ) = (p : ℕ) := q.2.eq_of_factorization_pos hne
        exact hqp (Subtype.ext hnat)
      simp [hzero]
    · intro hpnot
      have hpzero : m p = 0 := Finsupp.notMem_support_iff.mp hpnot
      simp [hpzero]
  · intro q _
    exact pow_ne_zero _ q.2.ne_zero

/-- Unique factorization makes finite prime products injective in their exponent vector. -/
theorem primeProduct_injective : Function.Injective primeProduct := by
  classical
  intro a b h
  ext p
  have hp := congrArg (fun n : ℕ => n.factorization (p : ℕ)) h
  simpa [primeProduct_factorization] using hp

/-- The same finite prime product, valued in `ℝ` for logarithms. -/
def primeProductReal (m : Nat.Primes →₀ ℕ) : ℝ :=
  m.prod fun p k => ((p : ℕ) : ℝ) ^ k

lemma primeProductReal_eq_natCast (m : Nat.Primes →₀ ℕ) :
    primeProductReal m = (primeProduct m : ℝ) := by
  unfold primeProductReal primeProduct
  rw [Nat.cast_finsuppProd]
  simp

lemma log_primeProduct (m : Nat.Primes →₀ ℕ) :
    Real.log (primeProduct m : ℝ) = m.sum fun p k => (k : ℝ) * Real.log (p : ℕ) := by
  rw [← primeProductReal_eq_natCast m]
  unfold primeProductReal
  rw [Finsupp.log_prod]
  · refine Finsupp.sum_congr ?_
    intro _ _
    rw [Real.log_pow]
  · intro p hzero
    have hpne : ((p : ℕ) : ℝ) ^ (m p) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)
    exact False.elim (hpne hzero)

lemma primeProduct_pos (m : Nat.Primes →₀ ℕ) : 0 < primeProduct m := by
  classical
  unfold primeProduct
  rw [Finsupp.prod]
  exact Finset.prod_pos fun p _ => pow_pos p.2.pos _

/-- Natural-coefficient log-prime relations are trivial. -/
theorem log_prime_nat_relation_eq (a b : Nat.Primes →₀ ℕ)
    (h : a.sum (fun p k => (k : ℝ) * Real.log (p : ℕ)) =
        b.sum (fun p k => (k : ℝ) * Real.log (p : ℕ))) :
    a = b := by
  apply primeProduct_injective
  have hlog : Real.log (primeProduct a : ℝ) = Real.log (primeProduct b : ℝ) := by
    rw [log_primeProduct, log_primeProduct]
    exact h
  have hreal : (primeProduct a : ℝ) = (primeProduct b : ℝ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (primeProduct_pos a)))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (primeProduct_pos b))) hlog
  exact_mod_cast hreal

lemma int_toNat_sub_neg_toNat (z : ℤ) :
    ((z.toNat : ℤ) - ((-z).toNat : ℤ)) = z := by
  omega

lemma real_max_int_cast_eq_toNat (z : ℤ) : max (z : ℝ) 0 = (z.toNat : ℝ) := by
  by_cases hz : 0 ≤ z
  · rw [max_eq_left]
    · exact_mod_cast (Int.toNat_of_nonneg hz).symm
    · exact_mod_cast hz
  · have hzle : z ≤ 0 := le_of_not_ge hz
    rw [max_eq_right]
    · rw [Int.toNat_eq_zero.mpr hzle]
      simp
    · exact_mod_cast hzle

/-- Positive part of an integer exponent vector. -/
def positivePart (m : Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℕ :=
  m.mapRange (fun z => z.toNat) (by simp)

/-- Negative part of an integer exponent vector. -/
def negativePart (m : Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℕ :=
  m.mapRange (fun z => (-z).toNat) (by simp)

def positivePartZ (m : Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℤ :=
  m.mapRange (fun z => (z.toNat : ℤ)) (by simp)

def negativePartZ (m : Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℤ :=
  m.mapRange (fun z => ((-z).toNat : ℤ)) (by simp)

lemma positivePartZ_sub_negativePartZ (m : Nat.Primes →₀ ℤ) :
    positivePartZ m - negativePartZ m = m := by
  ext
  simp [positivePartZ, negativePartZ]

lemma positivePartZ_sum (m : Nat.Primes →₀ ℤ) :
    (positivePartZ m).sum (fun p z => (z : ℝ) * Real.log (p : ℕ)) =
      (positivePart m).sum (fun p k => (k : ℝ) * Real.log (p : ℕ)) := by
  unfold positivePartZ positivePart
  rw [Finsupp.sum_mapRange_index, Finsupp.sum_mapRange_index]
  · refine Finsupp.sum_congr ?_
    intro p _
    norm_num
    exact Or.inl (real_max_int_cast_eq_toNat (m p))
  · intro p
    simp
  · intro p
    simp

lemma negativePartZ_sum (m : Nat.Primes →₀ ℤ) :
    (negativePartZ m).sum (fun p z => (z : ℝ) * Real.log (p : ℕ)) =
      (negativePart m).sum (fun p k => (k : ℝ) * Real.log (p : ℕ)) := by
  unfold negativePartZ negativePart
  rw [Finsupp.sum_mapRange_index, Finsupp.sum_mapRange_index]
  · refine Finsupp.sum_congr ?_
    intro p _
    norm_num
    exact Or.inl (by simpa using real_max_int_cast_eq_toNat (-(m p)))
  · intro p
    simp
  · intro p
    simp

/-- Integer-coefficient finite log-prime relations are trivial. -/
theorem log_prime_int_relation_eq_zero (m : Nat.Primes →₀ ℤ)
    (h : m.sum (fun p z => (z : ℝ) * Real.log (p : ℕ)) = 0) :
    m = 0 := by
  classical
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
  have hnat : (positivePart m).sum fNat = (negativePart m).sum fNat := by
    apply sub_eq_zero.mp
    rw [hdiff]
    exact h
  have hparts : positivePart m = negativePart m := log_prime_nat_relation_eq _ _ hnat
  ext p
  have hp : positivePart m p = negativePart m p := congrArg (fun f => f p) hparts
  have hpz : ((m p).toNat : ℤ) = ((-(m p)).toNat : ℤ) := by
    exact_mod_cast hp
  have hsub : ((m p).toNat : ℤ) - ((-(m p)).toNat : ℤ) = 0 := sub_eq_zero.mpr hpz
  rwa [int_toNat_sub_neg_toNat] at hsub

/-- The logarithms of primes are `ℤ`-linearly independent. -/
theorem logPrime_linearIndependent_int :
    LinearIndependent ℤ (fun p : Nat.Primes => Real.log (p : ℕ)) := by
  rw [linearIndependent_iff]
  intro l hl
  apply log_prime_int_relation_eq_zero
  rw [Finsupp.linearCombination_apply] at hl
  rw [← hl]
  refine Finsupp.sum_congr ?_
  intro p _
  rw [zsmul_eq_mul]

/-- The logarithms of primes are linearly independent over `ℚ`. -/
theorem linearIndependent_log_primes :
    LinearIndependent ℚ (fun p : Nat.Primes => Real.log (p : ℕ)) :=
  (logPrime_linearIndependent_int).localization ℚ (nonZeroDivisors ℤ)

end

end GaloisForLFunctions
