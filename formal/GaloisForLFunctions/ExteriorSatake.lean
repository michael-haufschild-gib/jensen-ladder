import Mathlib

/-!
# Exterior-power Satake: the local L-factor coefficients are the ∧ᵏ data (Tier A)

This file formalizes the exterior-power (`∧ᵏ`) face of branch B30
(`spectral-functoriality-operations-calculus.md`): the coefficients of the local
L-factor `∏_α (1 − α x)` are the **signed elementary symmetric functions**
`(−1)ᵏ · eₖ(α)`, i.e. the traces of the exterior-power Satake `∧ᵏπ`. This is the
`∧ᵏ`/elementary-symmetric companion of the trace/power-sum (`ψᵐ`, Adams) face in
`AdamsOperations.lean`: together they give the two standard bases of the
operations λ-ring on the Satake side.

Along the way we fill a mathlib gap: the **cons recursion for the multiset
elementary symmetric function** (`Multiset.esymm`), `eₖ₊₁(a ::ₘ s) = eₖ₊₁(s) + a·eₖ(s)`.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- **Elementary-symmetric cons recursion** (mathlib gap-fill). For a multiset `s`
and a new element `a`, `eₖ₊₁(a ::ₘ s) = eₖ₊₁(s) + a·eₖ(s)`: a `(k+1)`-subset either
omits `a` (`eₖ₊₁(s)`) or contains it (`a` times a `k`-subset of `s`). -/
theorem multiset_esymm_cons (a : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

/-- **B30 (∧ᵏ Satake = local L-factor coefficients).** The local L-factor
`∏_{α∈s}(1 − α·x)` has its coefficient of `xᵏ` equal to `(−1)ᵏ · eₖ(s)`, the
signed `k`-th elementary symmetric function — the trace of the exterior-power
(`∧ᵏ`) Satake. Proved by induction on `s` via `multiset_esymm_cons`. -/
theorem localFactor_coeff_esymm (s : Multiset ℂ) (k : ℕ) :
    ((s.map (fun a => 1 - C a * X)).prod).coeff k = (-1) ^ k * s.esymm k := by
  have he0 : ∀ u : Multiset ℂ, u.esymm 0 = 1 := fun u => by simp [Multiset.esymm]
  induction s using Multiset.induction generalizing k with
  | empty => rcases k with _ | m <;> simp [Multiset.esymm, Polynomial.coeff_one]
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    rcases k with _ | m
    · have h0 : ((1 - C a * X) * (t.map (fun a => 1 - C a * X)).prod).coeff 0
              = (t.map (fun a => 1 - C a * X)).prod.coeff 0 := by
        simp [Polynomial.coeff_zero_eq_eval_zero]
      rw [h0, ih 0, he0 t, he0 (a ::ₘ t)]
    · have hcoeff : ((1 - C a * X) * (t.map (fun a => 1 - C a * X)).prod).coeff (m + 1)
              = (t.map (fun a => 1 - C a * X)).prod.coeff (m + 1)
                - a * (t.map (fun a => 1 - C a * X)).prod.coeff m := by
        rw [sub_mul, one_mul, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_mul]
      rw [hcoeff, ih (m + 1), ih m, multiset_esymm_cons]
      ring

/-- **B30 (∧ⁿ Satake = central character).** The top elementary symmetric
function `e_{card}` is the product of all Satake parameters: `e_n(s) = ∏ s`. This
is the `∧ⁿ` (top exterior power = determinant) — the central character `det π` —
the `k = n` case of `localFactor_coeff_esymm` (the constant term of the
characteristic side / leading datum of the local L-factor). -/
theorem multiset_esymm_card_eq_prod (s : Multiset ℂ) :
    s.esymm s.card = s.prod := by
  simp [Multiset.esymm, Multiset.powersetCard_self]

/-- **∧ᵏ temperedness (Ramanujan bound for the exterior power).** For a unitary
Satake parameter list (all `‖α‖ ≤ 1`), the `∧ᵏ` datum `eₖ` is bounded by the
dimension of `∧ᵏ`: `‖eₖ(s)‖ ≤ binom(n, k)` where `n = card s`. Each of the
`binom(n,k)` `k`-subset products has norm `≤ 1`, so the triangle inequality gives
the bound — the exterior-power analogue of `SatakeInterval.symPower_trace_norm_le`. -/
theorem esymm_norm_le (s : Multiset ℂ) (hs : ∀ a ∈ s, ‖a‖ ≤ 1) (k : ℕ) :
    ‖s.esymm k‖ ≤ (s.card.choose k : ℝ) := by
  have hprod : ∀ m : Multiset ℂ, (∀ a ∈ m, ‖a‖ ≤ 1) → ‖m.prod‖ ≤ 1 := by
    intro m
    induction m using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        intro h
        rw [Multiset.prod_cons, norm_mul]
        exact mul_le_one₀ (h a (Multiset.mem_cons_self a t)) (norm_nonneg _)
          (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))
  rw [Multiset.esymm]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  calc (Multiset.map ((fun x => ‖x‖) ∘ Multiset.prod) (s.powersetCard k)).sum
      ≤ (Multiset.map (fun _ => (1 : ℝ)) (s.powersetCard k)).sum := by
        apply Multiset.sum_map_le_sum_map
        intro m hm
        simp only [Function.comp_apply]
        apply hprod
        intro a ha
        rw [Multiset.mem_powersetCard] at hm
        exact hs a (Multiset.mem_of_le hm.1 ha)
    _ = (s.card.choose k : ℝ) := by
        rw [Multiset.map_const', Multiset.sum_replicate, Multiset.card_powersetCard,
          nsmul_eq_mul, mul_one]

/-- **Power-sum / Adams temperedness (Ramanujan bound for `ψᵏ`).** For a unitary
Satake parameter list (all `‖α‖ ≤ 1`), the `k`-th power sum / Adams operation
`pₖ = Σ αᵏ` is bounded by the rank `n = card s`: `‖Σ_{α∈s} αᵏ‖ ≤ n`. Together with
`esymm_norm_le` (`∧ᵏ`) and `SatakeInterval.symPower_trace_norm_le` (`Symᵏ`) this
bounds all three standard λ-ring bases for tempered Satake data. -/
theorem multiset_powerSum_norm_le (s : Multiset ℂ) (hs : ∀ a ∈ s, ‖a‖ ≤ 1) (k : ℕ) :
    ‖(s.map (fun a => a ^ k)).sum‖ ≤ (s.card : ℝ) := by
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  calc (s.map ((fun x => ‖x‖) ∘ fun a => a ^ k)).sum
      ≤ (s.map (fun _ => (1 : ℝ))).sum := by
        apply Multiset.sum_map_le_sum_map
        intro a ha
        simp only [Function.comp_apply, norm_pow]
        exact pow_le_one₀ (norm_nonneg a) (hs a ha)
    _ = (s.card : ℝ) := by
        rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]

/-- **∧ᵏ vanishes above the rank.** The `k`-th elementary symmetric function is
zero once `k` exceeds the number of parameters: `eₖ(s) = 0` for `card s < k`.
This is `∧ᵏV = 0` for `k > dim V` — the local L-factor `∏(1−αx)` is a polynomial
of degree `≤ n`, so the exterior-power Satake `∧ᵏπ` is trivial above the rank. -/
theorem multiset_esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) :
    s.esymm k = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty k h, Multiset.map_zero, Multiset.sum_zero]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **The local factor has no coefficients above the Satake rank.** Since the coefficient of `x^k`
in `∏_{α∈s}(1-αx)` is `(-1)^k e_k(s)` and `e_k(s)=0` for `k>card s`, every coefficient above the
number of Satake parameters vanishes. This is the finite polynomial-degree bound for the exterior
Satake coefficient package. -/
theorem localFactor_coeff_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) :
    ((s.map (fun a => 1 - C a * X)).prod).coeff k = 0 := by
  rw [localFactor_coeff_esymm, multiset_esymm_eq_zero_of_card_lt s h, mul_zero]

end

end GaloisForLFunctions
