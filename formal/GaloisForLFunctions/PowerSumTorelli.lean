import GaloisForLFunctions.MultisetNewton

/-!
# Power-sum (secular-moment) Torelli — the B29 headline (Tier A)

This file completes branch B29 (`spectral-torelli-inverse-problem.md`) at the
**power-sum** level: the secular power sums `p_k = Σ_ρ ρ^k` faithfully determine
the zero multiset. This upgrades the polynomial/elementary-symmetric faithfulness
(`SpectralTorelli.spectralTorelli_faithful`) to the genuine secular-moment
statement of the field.

The proof runs the field's own program in Lean:
1. **Inversion** (`esymm_eq_of_powerSum_eq`): equal power sums force equal
   elementary symmetric functions, by strong induction on `k` through Newton's
   identity (`multiset_newton`), solving for `e_k` in characteristic zero
   (`k` invertible in `ℂ`).
2. **Tie** (`powerSum_torelli`): equal `e_k` give equal spectral polynomials
   `∏(X − ρ)` (their coefficients are `±e_k`, Vieta), hence equal zero multisets
   (`Polynomial.roots`).

It is stated for a finite family `f : Fin n → ℂ` (an enumerated zero
configuration); `Finset.univ.val.map f` is the zero multiset.
-/

open scoped BigOperators
open Finset GaloisForLFunctions Polynomial

namespace GaloisForLFunctions

noncomputable section

variable {n : ℕ}

/-- **Newton inversion.** If two finite families have equal power sums `Σ_i f(i)^k`
for all `k`, then their elementary symmetric functions agree for all `k`. Proved
by strong induction through `multiset_newton`, solving for `e_k` (char-zero: `k`
invertible). -/
theorem esymm_eq_of_powerSum_eq (f g : Fin n → ℂ)
    (hp : ∀ k, (univ.val.map (fun i => f i ^ k)).sum = (univ.val.map (fun i => g i ^ k)).sum) :
    ∀ k, (univ.val.map f).esymm k = (univ.val.map g).esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [Multiset.esymm]
    · have nf := multiset_newton f k hk
      have ng := multiset_newton g k hk
      have hS : (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                  (-1) ^ a.1 * (univ.val.map f).esymm a.1
                    * (univ.val.map (fun i => f i ^ a.2)).sum)
              = (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                  (-1) ^ a.1 * (univ.val.map g).esymm a.1
                    * (univ.val.map (fun i => g i ^ a.2)).sum) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo] at ha
        rw [IH a.1 ha.2.2, hp a.2]
      have heq : (-1:ℂ) ^ (k+1) * k * (univ.val.map f).esymm k
                   - (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                       (-1) ^ a.1 * (univ.val.map f).esymm a.1
                         * (univ.val.map (fun i => f i ^ a.2)).sum)
               = (-1:ℂ) ^ (k+1) * k * (univ.val.map g).esymm k
                   - (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                       (-1) ^ a.1 * (univ.val.map g).esymm a.1
                         * (univ.val.map (fun i => g i ^ a.2)).sum) := by
        rw [← nf, ← ng]; exact hp k
      rw [hS] at heq
      have hcancel : (-1:ℂ) ^ (k+1) * k * (univ.val.map f).esymm k
                   = (-1:ℂ) ^ (k+1) * k * (univ.val.map g).esymm k := by linear_combination heq
      have hknz : ((-1:ℂ) ^ (k+1) * (k:ℂ)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hk.ne')
      exact mul_left_cancel₀ hknz hcancel

/-- **Power-sum (secular-moment) Torelli — B29 headline.** Two finite families
`f, g : Fin n → ℂ` with equal power sums `Σ_i f(i)^k = Σ_i g(i)^k` for all `k`
have the same multiset of values: the secular power sums `p_k` faithfully
determine the zero multiset. The genuine secular-moment faithfulness of the
field, proved via Newton inversion + Vieta + `Polynomial.roots`. -/
theorem powerSum_torelli (f g : Fin n → ℂ)
    (hp : ∀ k, (univ.val.map (fun i => f i ^ k)).sum = (univ.val.map (fun i => g i ^ k)).sum) :
    univ.val.map f = univ.val.map g := by
  have he := esymm_eq_of_powerSum_eq f g hp
  have hcardf : (univ.val.map f).card = n := by rw [Multiset.card_map]; simp
  have hcardg : (univ.val.map g).card = n := by rw [Multiset.card_map]; simp
  have hpoly : ((univ.val.map f).map (fun a => X - C a)).prod
             = ((univ.val.map g).map (fun a => X - C a)).prod := by
    apply Polynomial.ext
    intro j
    by_cases hj : j ≤ n
    · rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcardf]; exact hj),
          Multiset.prod_X_sub_C_coeff _ (by rw [hcardg]; exact hj), hcardf, hcardg, he]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hcardf]; omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hcardg]; omega)]
  calc univ.val.map f
      = ((univ.val.map f).map (fun a => X - C a)).prod.roots :=
        (roots_multiset_prod_X_sub_C _).symm
    _ = ((univ.val.map g).map (fun a => X - C a)).prod.roots := by rw [hpoly]
    _ = univ.val.map g := roots_multiset_prod_X_sub_C _

/-- **Finite Newton inversion.** Only the first `n` power sums are needed: equal
power sums `p_k` for `k ≤ n` force equal elementary symmetric functions `e_k` for
`k ≤ n`. Same strong induction, tracking the bound `k ≤ n`. -/
theorem esymm_eq_of_powerSum_eq_le (f g : Fin n → ℂ)
    (hp : ∀ k, k ≤ n → (univ.val.map (fun i => f i ^ k)).sum
                      = (univ.val.map (fun i => g i ^ k)).sum) :
    ∀ k, k ≤ n → (univ.val.map f).esymm k = (univ.val.map g).esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [Multiset.esymm]
    · have nf := multiset_newton f k hk
      have ng := multiset_newton g k hk
      have hS : (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                  (-1) ^ a.1 * (univ.val.map f).esymm a.1
                    * (univ.val.map (fun i => f i ^ a.2)).sum)
              = (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                  (-1) ^ a.1 * (univ.val.map g).esymm a.1
                    * (univ.val.map (fun i => g i ^ a.2)).sum) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo] at ha
        obtain ⟨hsum, ha1pos, ha1lt⟩ := ha
        rw [IH a.1 ha1lt (by omega), hp a.2 (by omega)]
      have heq : (-1:ℂ) ^ (k+1) * k * (univ.val.map f).esymm k
                   - (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                       (-1) ^ a.1 * (univ.val.map f).esymm a.1
                         * (univ.val.map (fun i => f i ^ a.2)).sum)
               = (-1:ℂ) ^ (k+1) * k * (univ.val.map g).esymm k
                   - (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
                       (-1) ^ a.1 * (univ.val.map g).esymm a.1
                         * (univ.val.map (fun i => g i ^ a.2)).sum) := by
        rw [← nf, ← ng]; exact hp k hkn
      rw [hS] at heq
      have hcancel : (-1:ℂ) ^ (k+1) * k * (univ.val.map f).esymm k
                   = (-1:ℂ) ^ (k+1) * k * (univ.val.map g).esymm k := by linear_combination heq
      have hknz : ((-1:ℂ) ^ (k+1) * (k:ℂ)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hk.ne')
      exact mul_left_cancel₀ hknz hcancel

/-- **Power-sum Torelli, sharp finite form — "`n` secular moments determine `n`
zeros".** Two finite families `f, g : Fin n → ℂ` with equal power sums
`Σ_i f(i)^k = Σ_i g(i)^k` for just `k ≤ n` already have the same multiset of
values. This is the field's exact statement: the first `n` secular moments pin
down a configuration of `n` zeros. -/
theorem powerSum_torelli_finite (f g : Fin n → ℂ)
    (hp : ∀ k, k ≤ n → (univ.val.map (fun i => f i ^ k)).sum
                      = (univ.val.map (fun i => g i ^ k)).sum) :
    univ.val.map f = univ.val.map g := by
  have he := esymm_eq_of_powerSum_eq_le f g hp
  have hcardf : (univ.val.map f).card = n := by rw [Multiset.card_map]; simp
  have hcardg : (univ.val.map g).card = n := by rw [Multiset.card_map]; simp
  have hpoly : ((univ.val.map f).map (fun a => X - C a)).prod
             = ((univ.val.map g).map (fun a => X - C a)).prod := by
    apply Polynomial.ext
    intro j
    by_cases hj : j ≤ n
    · rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcardf]; exact hj),
          Multiset.prod_X_sub_C_coeff _ (by rw [hcardg]; exact hj), hcardf, hcardg,
          he (n - j) (by omega)]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hcardf]; omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hcardg]; omega)]
  calc univ.val.map f
      = ((univ.val.map f).map (fun a => X - C a)).prod.roots :=
        (roots_multiset_prod_X_sub_C _).symm
    _ = ((univ.val.map g).map (fun a => X - C a)).prod.roots := by rw [hpoly]
    _ = univ.val.map g := roots_multiset_prod_X_sub_C _

/-- **Secular moments separate configurations (B29, contrapositive).** Two
*distinct* zero configurations `f, g : Fin n → ℂ` are separated by some secular
moment of order `≤ n`: there is `k ≤ n` with `Σ_i f(i)^k ≠ Σ_i g(i)^k`. The
identifiability statement dual to `powerSum_torelli_finite`. -/
theorem exists_powerSum_ne_of_ne (f g : Fin n → ℂ)
    (h : univ.val.map f ≠ univ.val.map g) :
    ∃ k, k ≤ n ∧ (univ.val.map (fun i => f i ^ k)).sum
                 ≠ (univ.val.map (fun i => g i ^ k)).sum := by
  by_contra hc
  apply h
  apply powerSum_torelli_finite
  intro k hk
  by_contra hne
  exact hc ⟨k, hk, hne⟩

/-- **Secular-moment dictionary: the second Newton–Girard identity.** The second
elementary symmetric function (the `∧²` / `Sym`-quadratic secular datum) in terms
of the first two power sums: `2·e₂ = p₁² − p₂`, i.e.
`2·esymm₂ = (Σ_i f i)² − Σ_i (f i)²`. The explicit `k=2` instance of
`multiset_newton` (the antidiagonal filter collapses to the single term `(1,1)`),
with `e₁ = p₁` (`esymm 1 = sum`). -/
theorem secularMoment_girard_two (f : Fin n → ℂ) :
    2 * (univ.val.map f).esymm 2
      = ((univ.val.map f).sum) ^ 2 - (univ.val.map (fun i => f i ^ 2)).sum := by
  have he1 : ∀ s : Multiset ℂ, s.esymm 1 = s.sum :=
    fun s => by simp [Multiset.esymm, Multiset.powersetCard_one]
  have h := multiset_newton f 2 (by norm_num)
  rw [show {a ∈ antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} = ({(1, 1)} : Finset (ℕ × ℕ)) from by decide,
      Finset.sum_singleton] at h
  simp only [pow_one, he1] at h
  rw [show (fun x : Fin n => f x) = f from rfl] at h
  push_cast at h
  linear_combination h

/-- **Secular-moment dictionary: the third Newton–Girard identity.** The third
elementary symmetric function in terms of the first three power sums:
`6·e₃ = 2·p₃ − 3·p₁·p₂ + p₁³`. The `k=3` instance of `multiset_newton` (the
antidiagonal filter gives the two terms `(1,2),(2,1)`), combined with the `e₁`
and `e₂` identities. Demonstrates the Newton engine scales to all orders. -/
theorem secularMoment_girard_three (f : Fin n → ℂ) :
    6 * (univ.val.map f).esymm 3
      = 2 * (univ.val.map (fun i => f i ^ 3)).sum
        - 3 * (univ.val.map f).sum * (univ.val.map (fun i => f i ^ 2)).sum
        + (univ.val.map f).sum ^ 3 := by
  have he1 : ∀ s : Multiset ℂ, s.esymm 1 = s.sum :=
    fun s => by simp [Multiset.esymm, Multiset.powersetCard_one]
  have hg2 := secularMoment_girard_two f
  have h := multiset_newton f 3 (by norm_num)
  rw [show {a ∈ antidiagonal 3 | a.1 ∈ Set.Ioo 0 3}
        = ({(1, 2), (2, 1)} : Finset (ℕ × ℕ)) from by decide,
      Finset.sum_pair (by decide : ((1, 2) : ℕ × ℕ) ≠ (2, 1))] at h
  simp only [pow_one, he1] at h
  rw [show (fun x : Fin n => f x) = f from rfl] at h
  push_cast at h
  linear_combination -2 * h + (univ.val.map f).sum * hg2

end

end GaloisForLFunctions
