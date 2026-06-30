import Mathlib
import JensenLadder.T3T5SumRule
import JensenLadder.WeilFluctuationLoewner

/-!
# Secular ground state: strict monotonicity and uniqueness below the poles

The CCM/Cauchy reconstruction of Stage 1 of the T3/T5 construction sub-program
(`docs/plans/program_T3_T5_self_product_construction_20260617.md` §50–51) is governed by the
**secular equation**

`S(z) = ∑ₙ aₙ / (dₙ − z) = 1`,   `dₙ = 2πn/L`  the grid poles,  `aₙ > 0`  the prime/Euler-loaded source weights.

Its solutions are the reconstructed spectrum (`SecularReconstruction`). This file establishes the
**ground-state** structure that underlies the CCM ζ-bottom certification (the bottom of the spectrum
is the unique secular root lying below all poles):

* `secular_strictMono_below_poles` — with positive weights, `S` is **strictly increasing** on the
  region below every pole (each term `z ↦ aₙ/(dₙ − z)` is increasing there; no calculus needed —
  only `div_lt_div_of_pos_left` and `Finset.sum_lt_sum_of_nonempty`);
* `secular_below_poles_unique` — hence `S` is **injective** below the poles, so the secular equation
  `S(z) = c` has **at most one** solution there: the ground-state / bottom root is unique.

RH-free; pure real analysis. Axiom-clean. The sign/no-margin question (whether the bottom root
realizes Weil positivity) is *not* addressed here — this is purely the ordering structure of the
Cauchy/Aronszajn kernel.
-/

namespace JensenLadder
namespace SecularGroundState

/-- **Secular function strict monotonicity below the poles.** For positive weights `a i > 0` and a
point `z₂` lying strictly below every pole `d i`, increasing the argument from `z₁` to `z₂` strictly
increases the secular sum: `∑ᵢ aᵢ/(dᵢ − z₁) < ∑ᵢ aᵢ/(dᵢ − z₂)`. Each summand is increasing because a
larger argument shrinks the positive denominator `dᵢ − z`. RH-free. Axiom-clean. -/
theorem secular_strictMono_below_poles {ι : Type*} [Fintype ι] [Nonempty ι]
    {a d : ι → ℝ} (ha : ∀ i, 0 < a i) {z₁ z₂ : ℝ} (h12 : z₁ < z₂)
    (hz : ∀ i, z₂ < d i) :
    (∑ i, a i / (d i - z₁)) < ∑ i, a i / (d i - z₂) := by
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hb : 0 < d i - z₂ := by linarith [hz i]
  have hbc : d i - z₂ < d i - z₁ := by linarith
  exact div_lt_div_of_pos_left (ha i) hb hbc

/-- **Uniqueness of the ground-state root.** Strict monotonicity makes the secular function injective
below all poles: if two points `z₁, z₂` both lie below every pole and give equal secular values, they
coincide. In particular the secular equation `S(z) = 1` has at most one solution below the spectrum —
the bottom/ground-state root is unique (the ordering fact behind the CCM ζ-bottom certification).
RH-free. Axiom-clean. -/
theorem secular_below_poles_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    {a d : ι → ℝ} (ha : ∀ i, 0 < a i) {z₁ z₂ : ℝ}
    (hz₁ : ∀ i, z₁ < d i) (hz₂ : ∀ i, z₂ < d i)
    (hS : (∑ i, a i / (d i - z₁)) = ∑ i, a i / (d i - z₂)) : z₁ = z₂ := by
  rcases lt_trichotomy z₁ z₂ with h | h | h
  · exact absurd hS (ne_of_lt (secular_strictMono_below_poles ha h hz₂))
  · exact h
  · exact absurd hS.symm (ne_of_lt (secular_strictMono_below_poles ha h hz₁))

/-- **Secular interlacing engine: strict monotonicity on any pole-free interval.** Generalizing
`secular_strictMono_below_poles` from "below all poles" to *any* interval `[z₁, z₂]` containing no
pole. The clean uniform hypothesis is that each pole sits strictly outside the interval, i.e. the two
denominators have the same sign: `0 < (dᵢ − z₁)(dᵢ − z₂)`. Then `S` is strictly increasing:
`∑ aᵢ/(dᵢ−z₁) < ∑ aᵢ/(dᵢ−z₂)`. Proof: each summand difference is
`aᵢ(z₂−z₁) / ((dᵢ−z₂)(dᵢ−z₁)) > 0` (positive numerator over a positive same-sign product). This is the
ordering engine of secular *interlacing* — `S` rises monotonically across every gap between
consecutive poles. RH-free. Axiom-clean. -/
theorem secular_strictMono_off_poles {ι : Type*} [Fintype ι] [Nonempty ι]
    {a d : ι → ℝ} (ha : ∀ i, 0 < a i) {z₁ z₂ : ℝ} (h12 : z₁ < z₂)
    (hgap : ∀ i, 0 < (d i - z₁) * (d i - z₂)) :
    (∑ i, a i / (d i - z₁)) < ∑ i, a i / (d i - z₂) := by
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hd1 : d i - z₁ ≠ 0 := left_ne_zero_of_mul (hgap i).ne'
  have hd2 : d i - z₂ ≠ 0 := right_ne_zero_of_mul (hgap i).ne'
  have hpos : 0 < a i / (d i - z₂) - a i / (d i - z₁) := by
    rw [div_sub_div _ _ hd2 hd1]
    apply div_pos
    · nlinarith [ha i, h12]
    · rw [mul_comm]; exact hgap i
  linarith

/-- **Interlacing uniqueness: at most one root per gap.** Since the same-sign hypothesis
`0 < (dᵢ − z₁)(dᵢ − z₂)` is symmetric in `z₁, z₂`, strict monotonicity makes `S` injective on any
pole-free interval: equal secular values at two such points force the points to coincide. Hence the
secular equation `S(z) = 1` has **at most one solution in each gap** between consecutive poles — the
roots interlace the poles. RH-free. Axiom-clean. -/
theorem secular_off_poles_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    {a d : ι → ℝ} (ha : ∀ i, 0 < a i) {z₁ z₂ : ℝ}
    (hgap : ∀ i, 0 < (d i - z₁) * (d i - z₂))
    (hS : (∑ i, a i / (d i - z₁)) = ∑ i, a i / (d i - z₂)) : z₁ = z₂ := by
  rcases lt_trichotomy z₁ z₂ with h | h | h
  · exact absurd hS (ne_of_lt (secular_strictMono_off_poles ha h hgap))
  · exact h
  · have hgap' : ∀ i, 0 < (d i - z₂) * (d i - z₁) := fun i => by rw [mul_comm]; exact hgap i
    exact absurd hS.symm (ne_of_lt (secular_strictMono_off_poles ha h hgap'))

/-- **Existence of a secular root (intermediate value).** On a pole-free closed interval `[z₁, z₂]`
(no `dᵢ` lies in it), if the secular sum straddles the target — `S(z₁) ≤ 1 ≤ S(z₂)` — then `S(z) = 1`
has a solution in `[z₁, z₂]`. Proof: `S` is `ContinuousOn` the interval (finite sum of `aᵢ/(dᵢ−z)`,
each continuous since `dᵢ − z ≠ 0`), so `intermediate_value_Icc` applies. RH-free. Axiom-clean. -/
theorem secular_root_exists {ι : Type*} [Fintype ι] {a d : ι → ℝ} {z₁ z₂ : ℝ} (h12 : z₁ ≤ z₂)
    (hpole : ∀ i, ∀ z ∈ Set.Icc z₁ z₂, d i - z ≠ 0)
    (hlo : (∑ i, a i / (d i - z₁)) ≤ 1) (hhi : 1 ≤ ∑ i, a i / (d i - z₂)) :
    ∃ z ∈ Set.Icc z₁ z₂, (∑ i, a i / (d i - z)) = 1 := by
  have hcont : ContinuousOn (fun z => ∑ i, a i / (d i - z)) (Set.Icc z₁ z₂) := by
    apply continuousOn_finsetSum
    intro i _
    have hg : ContinuousOn (fun z => d i - z) (Set.Icc z₁ z₂) :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hg (fun z hz => hpole i z hz)
  have hmem : (1:ℝ) ∈ Set.Icc ((fun z => ∑ i, a i / (d i - z)) z₁)
      ((fun z => ∑ i, a i / (d i - z)) z₂) := Set.mem_Icc.mpr ⟨hlo, hhi⟩
  obtain ⟨z, hz, hzeq⟩ := intermediate_value_Icc h12 hcont hmem
  exact ⟨z, hz, hzeq⟩

/-- **Interlacing: exactly one secular root per gap.** Combining existence (`secular_root_exists`,
via IVT) with uniqueness (`secular_off_poles_unique`, via strict monotonicity): on a pole-free closed
interval `[z₁, z₂]` with positive weights, if `S` straddles `1` then `S(z) = 1` has a **unique**
solution there. (The same-sign hypothesis of uniqueness is supplied by "no pole in `[z₁,z₂]`": every
`dᵢ` lies strictly below `z₁` or strictly above `z₂`, so `(dᵢ − z)(dᵢ − z') > 0` for any two interior
points.) This is the full interlacing statement of the Stage-1 secular spectrum: one root per gap
between consecutive poles. RH-free. Axiom-clean. -/
theorem secular_root_unique_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    {a d : ι → ℝ} {z₁ z₂ : ℝ} (ha : ∀ i, 0 < a i) (h12 : z₁ ≤ z₂)
    (hpole : ∀ i, ∀ z ∈ Set.Icc z₁ z₂, d i - z ≠ 0)
    (hlo : (∑ i, a i / (d i - z₁)) ≤ 1) (hhi : 1 ≤ ∑ i, a i / (d i - z₂)) :
    ∃! z, z ∈ Set.Icc z₁ z₂ ∧ (∑ i, a i / (d i - z)) = 1 := by
  obtain ⟨z₀, hz₀, hz₀eq⟩ := secular_root_exists h12 hpole hlo hhi
  refine ⟨z₀, ⟨hz₀, hz₀eq⟩, ?_⟩
  rintro z ⟨hz, hzeq⟩
  refine secular_off_poles_unique ha ?_ (hzeq.trans hz₀eq.symm)
  intro i
  have hnotin : d i ∉ Set.Icc z₁ z₂ := fun hmem => hpole i (d i) hmem (sub_self (d i))
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnotin
  rw [Set.mem_Icc] at hz hz₀
  rcases hnotin with hlt | hgt
  · have h1 : d i - z < 0 := by linarith [hz.1]
    have h2 : d i - z₀ < 0 := by linarith [hz₀.1]
    exact mul_pos_of_neg_of_neg h1 h2
  · have h1 : 0 < d i - z := by linarith [hz.2]
    have h2 : 0 < d i - z₀ := by linarith [hz₀.2]
    exact mul_pos h1 h2

open Filter Topology in
/-- **Pole divergence (left end of a gap): `S → −∞`.** A single secular term with positive weight
diverges to `−∞` as the argument approaches its pole from above: `a/(c − z) → −∞` as `z ↓ c`
(then `c − z → 0⁻`, so `(c−z)⁻¹ → atBot`, scaled by `a > 0`). This is the divergence that makes the
straddle hypothesis of `secular_root_exists` automatic at the *left* end of each gap (just above the
lower pole, the secular sum is eventually below any target). RH-free. Axiom-clean. -/
theorem secular_term_tendsto_atBot {a c : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun z => a / (c - z)) (𝓝[>] c) Filter.atBot := by
  have hsub : Filter.Tendsto (fun z => c - z) (𝓝[>] c) (𝓝[<] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨((continuous_const.sub continuous_id).tendsto' c 0 (by simp)).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_Iio]; simp only [Set.mem_Ioi] at hz; linarith
  have hinv := tendsto_inv_nhdsLT_zero.comp hsub
  simpa only [div_eq_mul_inv] using Filter.Tendsto.const_mul_atBot ha hinv

open Filter Topology in
/-- **Pole divergence (right end of a gap): `S → +∞`.** The companion: `a/(c − z) → +∞` as `z ↑ c`
(then `c − z → 0⁺`, so `(c−z)⁻¹ → atTop`, scaled by `a > 0`). This makes the straddle hypothesis
automatic at the *right* end of each gap (just below the upper pole, the secular sum is eventually
above any target). Together with `secular_term_tendsto_atBot` and `secular_root_unique_exists`, the
unconditional "exactly one root strictly inside each gap" follows once the bounded remainder terms are
controlled (distinct poles). RH-free. Axiom-clean. -/
theorem secular_term_tendsto_atTop {a c : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun z => a / (c - z)) (𝓝[<] c) Filter.atTop := by
  have hsub : Filter.Tendsto (fun z => c - z) (𝓝[<] c) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨((continuous_const.sub continuous_id).tendsto' c 0 (by simp)).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_Ioi]; simp only [Set.mem_Iio] at hz; linarith
  have hinv := tendsto_inv_nhdsGT_zero.comp hsub
  simpa only [div_eq_mul_inv] using Filter.Tendsto.const_mul_atTop ha hinv

open Filter Topology in
/-- **Full secular sum diverges to `−∞` at the lower end of a gap.** For positive weights and
*distinct* poles (`d` injective), the whole secular sum `∑ᵢ aᵢ/(dᵢ − z) → −∞` as `z ↓ dₖ`: the
`k`-th term diverges to `−∞` (`secular_term_tendsto_atBot`) while every other term is continuous at
`dₖ` (since `dᵢ ≠ dₖ`), so the remainder tends to a finite limit; `Tendsto.atBot_add` combines them.
This makes the lower-straddle hypothesis (`S(z) ≤ 1` for some `z` just above `dₖ`) **automatic**.
RH-free. Axiom-clean. -/
theorem secular_sum_tendsto_atBot {ι : Type*} [Fintype ι] [DecidableEq ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hd : Function.Injective d) (k : ι) :
    Filter.Tendsto (fun z => ∑ i, a i / (d i - z)) (𝓝[>] (d k)) Filter.atBot := by
  have hsplit : (fun z => ∑ i, a i / (d i - z))
      = fun z => a k / (d k - z) + ∑ i ∈ Finset.univ.erase k, a i / (d i - z) := by
    funext z; exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)).symm
  rw [hsplit]
  have hrest : Filter.Tendsto (fun z => ∑ i ∈ Finset.univ.erase k, a i / (d i - z))
      (𝓝[>] (d k)) (𝓝 (∑ i ∈ Finset.univ.erase k, a i / (d i - d k))) := by
    apply tendsto_finsetSum
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hne : d i - d k ≠ 0 := sub_ne_zero.mpr (hd.ne hik)
    have hca : ContinuousAt (fun z => a i / (d i - z)) (d k) :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  exact Filter.Tendsto.atBot_add (secular_term_tendsto_atBot (ha k)) hrest

open Filter Topology in
/-- **Full secular sum diverges to `+∞` at the upper end of a gap.** The companion to
`secular_sum_tendsto_atBot`: for positive weights and distinct poles, `∑ᵢ aᵢ/(dᵢ − z) → +∞` as
`z ↑ dₖ`. Together they make the straddle hypothesis of `secular_root_unique_exists` automatic on the
interior of every gap `(dₖ, dₖ₊₁)`: choosing endpoints close enough to the poles, `S` runs from below
`1` to above `1`, so **exactly one secular root sits strictly inside each gap** — fully unconditional
interlacing of the Stage-1 spectrum. RH-free. Axiom-clean. -/
theorem secular_sum_tendsto_atTop {ι : Type*} [Fintype ι] [DecidableEq ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hd : Function.Injective d) (k : ι) :
    Filter.Tendsto (fun z => ∑ i, a i / (d i - z)) (𝓝[<] (d k)) Filter.atTop := by
  have hsplit : (fun z => ∑ i, a i / (d i - z))
      = fun z => a k / (d k - z) + ∑ i ∈ Finset.univ.erase k, a i / (d i - z) := by
    funext z; exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)).symm
  rw [hsplit]
  have hrest : Filter.Tendsto (fun z => ∑ i ∈ Finset.univ.erase k, a i / (d i - z))
      (𝓝[<] (d k)) (𝓝 (∑ i ∈ Finset.univ.erase k, a i / (d i - d k))) := by
    apply tendsto_finsetSum
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hne : d i - d k ≠ 0 := sub_ne_zero.mpr (hd.ne hik)
    have hca : ContinuousAt (fun z => a i / (d i - z)) (d k) :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  exact Filter.Tendsto.atTop_add (secular_term_tendsto_atTop (ha k)) hrest

open Filter Topology in
/-- **Interlacing capstone: exactly one secular root per gap (unconditional).** For positive weights
and distinct poles, given two poles `d k < d m` with **no pole strictly between them**
(`∀ i, d i ≤ d k ∨ d m ≤ d i`), the secular equation `∑ᵢ aᵢ/(dᵢ − z) = 1` has a **unique** solution
in the open gap `(d k, d m)`. No straddle hypothesis is needed: the sum diverges to `−∞` just above
`d k` and to `+∞` just below `d m` (`secular_sum_tendsto_atBot`/`atTop`), so concrete straddle
endpoints `z_lo ∈ (d k, mid)`, `z_hi ∈ (mid, d m)` are extracted from those filters
(`Eventually.exists` + `eventually_lt_nhds`/`eventually_gt_nhds`); `secular_root_exists` (IVT) gives a
root on `[z_lo, z_hi] ⊆ (d k, d m)`, and `secular_off_poles_unique` gives uniqueness across the whole
gap (every pole lies outside, so the same-sign condition holds for any two interior points).

This is the complete, unconditional Cauchy/Aronszajn interlacing of the Stage-1 secular spectrum: one
root strictly inside each gap between consecutive poles. RH-free. Axiom-clean. The no-margin (whether
the relevant root realizes Weil positivity) is untouched = RH. -/
theorem secular_root_in_gap {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hd : Function.Injective d) {k m : ι} (hkm : d k < d m)
    (hgap : ∀ i, d i ≤ d k ∨ d m ≤ d i) :
    ∃! z, z ∈ Set.Ioo (d k) (d m) ∧ (∑ i, a i / (d i - z)) = 1 := by
  have hkmid : d k < (d k + d m) / 2 := by linarith
  have hmidm : (d k + d m) / 2 < d m := by linarith
  obtain ⟨zlo, hzlo1, hzloL, hzloR⟩ :
      ∃ zlo, (∑ i, a i / (d i - zlo)) ≤ 1 ∧ d k < zlo ∧ zlo < (d k + d m) / 2 := by
    have e1 := (tendsto_atBot.1 (secular_sum_tendsto_atBot ha hd k)) 1
    have e2 : ∀ᶠ z in 𝓝[>] (d k), z < (d k + d m) / 2 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hkmid)
    obtain ⟨zlo, h1, h2, h3⟩ := (e1.and (e2.and self_mem_nhdsWithin)).exists
    exact ⟨zlo, h1, h3, h2⟩
  obtain ⟨zhi, hzhi1, hzhiL, hzhiR⟩ :
      ∃ zhi, 1 ≤ (∑ i, a i / (d i - zhi)) ∧ (d k + d m) / 2 < zhi ∧ zhi < d m := by
    have e1 := (tendsto_atTop.1 (secular_sum_tendsto_atTop ha hd m)) 1
    have e2 : ∀ᶠ z in 𝓝[<] (d m), (d k + d m) / 2 < z :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hmidm)
    obtain ⟨zhi, h1, h2, h3⟩ := (e1.and (e2.and self_mem_nhdsWithin)).exists
    exact ⟨zhi, h1, h2, h3⟩
  have hlolt : zlo ≤ zhi := le_of_lt (lt_trans hzloR hzhiL)
  have hpolefree : ∀ i, ∀ z ∈ Set.Icc zlo zhi, d i - z ≠ 0 := by
    intro i z hz
    rcases hgap i with hle | hge
    · exact sub_ne_zero.mpr (ne_of_lt (by have := hz.1; linarith))
    · exact sub_ne_zero.mpr (ne_of_gt (by have := hz.2; linarith))
  obtain ⟨z0, hz0mem, hz0eq⟩ := secular_root_exists hlolt hpolefree hzlo1 hzhi1
  have hz0Ioo : z0 ∈ Set.Ioo (d k) (d m) :=
    ⟨by have := hz0mem.1; linarith, by have := hz0mem.2; linarith⟩
  refine ⟨z0, ⟨hz0Ioo, hz0eq⟩, ?_⟩
  rintro z ⟨hzIoo, hzeq⟩
  apply secular_off_poles_unique ha ?_ (hzeq.trans hz0eq.symm)
  intro i
  rcases hgap i with hle | hge
  · exact mul_pos_of_neg_of_neg (by have := hzIoo.1; linarith) (by have := hz0Ioo.1; linarith)
  · exact mul_pos (by have := hzIoo.2; linarith) (by have := hz0Ioo.2; linarith)

open Filter Topology in
/-- **Secular term vanishes at `−∞`.** `a/(c − z) → 0` as `z → −∞` (then `c − z → +∞`, and the
reciprocal `→ 0`). RH-free. Axiom-clean. -/
theorem secular_term_tendsto_zero {a c : ℝ} :
    Filter.Tendsto (fun z => a / (c - z)) Filter.atBot (𝓝 0) := by
  have hsub : Filter.Tendsto (fun z : ℝ => c - z) Filter.atBot Filter.atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left Filter.atBot c tendsto_neg_atBot_atTop
  have hinv : Filter.Tendsto (fun z => (c - z)⁻¹) Filter.atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsub
  have h := hinv.const_mul a
  rw [mul_zero] at h
  simpa only [div_eq_mul_inv] using h

open Filter Topology in
/-- **Full secular sum vanishes at `−∞`.** `∑ᵢ aᵢ/(dᵢ − z) → 0` as `z → −∞` (finite sum of terms
each `→ 0`). This is the lower-end behavior of the ground-state region `(−∞, min dᵢ)`. RH-free.
Axiom-clean. -/
theorem secular_sum_tendsto_zero {ι : Type*} [Fintype ι] {a d : ι → ℝ} :
    Filter.Tendsto (fun z => ∑ i, a i / (d i - z)) Filter.atBot (𝓝 0) := by
  simpa using tendsto_finsetSum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => secular_term_tendsto_zero (a := a i) (c := d i))

open Filter Topology in
/-- **Ground-state root: unique below the minimum pole (= the CCM ζ-bottom).** For positive weights
and distinct poles, if `d m` is the smallest pole (`∀ i, d m ≤ d i`), then the secular equation
`∑ᵢ aᵢ/(dᵢ − z) = 1` has a **unique** solution below `d m`. Unconditional: the sum runs from `0`
(at `−∞`, `secular_sum_tendsto_zero`) up to `+∞` (just below `d m`, `secular_sum_tendsto_atTop`),
crossing `1` exactly once. Existence by IVT on `[z_lo, z_hi]` with `z_lo` far below (where `S < 1`)
and `z_hi` just under `d m` (where `S > 1`); uniqueness by `secular_off_poles_unique` (all poles lie
above the region). This is the bottom of the reconstructed spectrum — the certified ground state of
the Stage-1 CCM secular operator. RH-free. Axiom-clean. The no-margin (whether this bottom root
realizes Weil positivity) is untouched = RH. -/
theorem secular_ground_state {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hd : Function.Injective d) {m : ι} (hm : ∀ i, d m ≤ d i) :
    ∃! z, z < d m ∧ (∑ i, a i / (d i - z)) = 1 := by
  obtain ⟨zhi, hzhi1, hzhiR⟩ : ∃ zhi, 1 ≤ (∑ i, a i / (d i - zhi)) ∧ zhi < d m := by
    have e1 := (tendsto_atTop.1 (secular_sum_tendsto_atTop ha hd m)) 1
    obtain ⟨zhi, h1, h2⟩ := (e1.and self_mem_nhdsWithin).exists
    exact ⟨zhi, h1, h2⟩
  obtain ⟨zlo, hzlo1, hzloLt⟩ : ∃ zlo, (∑ i, a i / (d i - zlo)) ≤ 1 ∧ zlo < zhi := by
    have e1 : ∀ᶠ z in Filter.atBot, (∑ i, a i / (d i - z)) < 1 :=
      secular_sum_tendsto_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
    obtain ⟨zlo, h1, h2⟩ := (e1.and (eventually_lt_atBot zhi)).exists
    exact ⟨zlo, le_of_lt h1, h2⟩
  have hlolt : zlo ≤ zhi := le_of_lt hzloLt
  have hpolefree : ∀ i, ∀ z ∈ Set.Icc zlo zhi, d i - z ≠ 0 := by
    intro i z hz
    exact sub_ne_zero.mpr (ne_of_gt (by have := hz.2; have := hm i; linarith))
  obtain ⟨z0, hz0mem, hz0eq⟩ := secular_root_exists hlolt hpolefree hzlo1 hzhi1
  have hz0lt : z0 < d m := by have := hz0mem.2; linarith
  refine ⟨z0, ⟨hz0lt, hz0eq⟩, ?_⟩
  rintro z ⟨hzlt, hzeq⟩
  apply secular_off_poles_unique ha ?_ (hzeq.trans hz0eq.symm)
  intro i
  exact mul_pos (by have := hm i; linarith) (by have := hm i; linarith)

/-- **Above the top pole the secular sum is negative.** For positive weights, if `d M` is the largest
pole (`∀ i, d i ≤ d M`) then for any `z` strictly above it the secular sum is `< 0`: every term
`aᵢ/(dᵢ − z)` has a positive numerator over a negative denominator (`dᵢ ≤ d M < z`). RH-free.
Axiom-clean. -/
theorem secular_neg_above_max {ι : Type*} [Fintype ι] [Nonempty ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) {M : ι} (hM : ∀ i, d i ≤ d M) {z : ℝ} (hz : d M < z) :
    (∑ i, a i / (d i - z)) < 0 := by
  have key : ∀ i ∈ Finset.univ, a i / (d i - z) < 0 := by
    intro i _
    have hdi : d i - z < 0 := by have := hM i; linarith
    exact div_neg_of_pos_of_neg (ha i) hdi
  calc (∑ i, a i / (d i - z))
      < ∑ _i : ι, (0:ℝ) := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty key
    _ = 0 := by simp

/-- **No secular root above the top pole (spectrum bounded above).** Immediate from
`secular_neg_above_max`: since `S(z) < 0 < 1` for `z` above the largest pole, `S(z) = 1` has no
solution there. Combined with `secular_ground_state` (a unique root below the smallest pole) and
`secular_root_in_gap` (exactly one root per interior gap), this confines the entire reconstructed
spectrum to `(−∞, max pole)` — every root is the ground state or an interior-gap root, none above.
RH-free. Axiom-clean. -/
theorem secular_no_root_above_max {ι : Type*} [Fintype ι] [Nonempty ι] {a d : ι → ℝ}
    (ha : ∀ i, 0 < a i) {M : ι} (hM : ∀ i, d i ≤ d M) {z : ℝ} (hz : d M < z) :
    (∑ i, a i / (d i - z)) ≠ 1 := by
  have := secular_neg_above_max ha hM hz; linarith

/-- **The shifted diagonal is `diag d − z·I`.** `diagonal (fun i => d i − z) = diagonal d − z • 1`.
The poles `dᵢ` of the secular function are exactly the diagonal entries — the eigenvalues of the
diagonal operator `diagonal d`. RH-free. Axiom-clean. -/
theorem diagonal_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (z : ℝ) :
    Matrix.diagonal (fun i => d i - z) = Matrix.diagonal d - z • (1 : Matrix ι ι ℝ) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h]

open Matrix in
/-- **Secular sum = diagonal resolvent quadratic form (the operator bridge).** With weights
`aᵢ = uᵢ²`, the secular function is literally the resolvent quadratic form of the diagonal operator
`diagonal d` at `z`:
`u ⬝ᵥ (diagonal (fun i => (dᵢ − z)⁻¹)) *ᵥ u = ∑ᵢ uᵢ²/(dᵢ − z) = S(z)`.
Since `diagonal (fun i => (dᵢ − z)⁻¹)` is the inverse of `diagonal d − z·1`
(`diagonal_sub_smul_one`, `Matrix.inv_diagonal`) off the poles, this identifies `S(z)` with
`uᵀ (diag d − z)⁻¹ u` — exactly the scalar in the Sherman–Morrison/no-margin threshold
(`T3T5SumRule.nomargin_threshold`: `det(ρ u uᵀ − M) = 0 ↔ ρ · uᵀ M⁻¹ u = 1`). So the secular
interlacing proved here (`secular_root_in_gap`, `secular_ground_state`) is the interlacing of the
resolvent of a diagonal operator under a rank-one source — grounding the abstract Stage-1 spectrum in
genuine operator theory. RH-free. Axiom-clean. -/
theorem secular_eq_diagonal_resolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (z : ℝ) :
    u ⬝ᵥ (Matrix.diagonal (fun i => (d i - z)⁻¹) *ᵥ u) = ∑ i, u i ^ 2 / (d i - z) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv, sq]; ring

/-- **Secular root ⟺ Weil determinant vanishes (the no-margin bridge).** For `z` not a pole
(`∀ i, d i − z ≠ 0`), the finite Weil determinant of `T3T5SumRule` with intersection form
`M = diagonal (fun i => d i − z) = diag d − z·1` vanishes **iff** the secular sum hits the threshold:
`det(ρ · u uᵀ − (diag d − z)) = 0 ↔ ρ · (∑ᵢ uᵢ²/(dᵢ − z)) = 1`.

So `z` is a generalized eigenvalue of the pencil `(ρ u uᵀ, diag d)` exactly when `ρ·S(z) = 1` — i.e.
the **secular roots are precisely the zeros of the Weil/no-margin determinant**. This fuses the two
session threads: the interlacing/ground-state geometry (`secular_root_in_gap`, `secular_ground_state`)
now describes the spectrum of the rank-one-perturbed diagonal operator whose bottom-eigenvalue
crossing is `T3T5SumRule.nomargin_threshold` (`S = 1` = the no-margin). Proof: `nomargin_threshold`
with `M = diag(d−z)` (invertible off the poles, `det = ∏(dᵢ−z) ≠ 0`), `M⁻¹ = diag((dᵢ−z)⁻¹)` via
`inv_eq_right_inv`, then `secular_eq_diagonal_resolvent`. RH-free. Axiom-clean. The *sign* of the
crossing (does the bottom root sit where `λ_min ≥ 0`) is untouched = RH. -/
theorem secular_root_iff_weil_det_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (z ρ : ℝ) (hpole : ∀ i, d i - z ≠ 0) :
    (ρ • Matrix.vecMulVec u u - Matrix.diagonal (fun i => d i - z)).det = 0
      ↔ ρ * (∑ i, u i ^ 2 / (d i - z)) = 1 := by
  have hdet : IsUnit (Matrix.diagonal (fun i => d i - z)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hpole i))
  have Minv : (Matrix.diagonal (fun i => d i - z))⁻¹ = Matrix.diagonal (fun i => (d i - z)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (d i - z) * (d i - z)⁻¹) = (fun _ : ι => (1:ℝ)) :=
      funext (fun i => mul_inv_cancel₀ (hpole i))
    rw [h1, Matrix.diagonal_one]
  rw [JensenLadder.T3T5SumRule.nomargin_threshold (Matrix.diagonal (fun i => d i - z)) hdet u ρ,
      Minv, secular_eq_diagonal_resolvent]

/-- **Secular roots = eigenvalues of the rank-one-perturbed diagonal.** For `z` not a pole, `z` is an
eigenvalue of `diag d − ρ·u uᵀ` (`det((diag d − ρ u uᵀ) − z·1) = 0`) **iff** `ρ·S(z) = 1`, where
`S(z) = ∑ᵢ uᵢ²/(dᵢ − z)`. Proof: `(diag d − ρ u uᵀ) − z·1 = −(ρ u uᵀ − (diag d − z·1))`
(`diagonal_sub_smul_one` + `abel`), so the determinants agree up to the unit `(−1)^card`
(`Matrix.det_neg`); apply `secular_root_iff_weil_det_zero`.

This is the classical secular-equation theorem, now formal: **the spectrum of a rank-one perturbation
of a diagonal operator is exactly the secular root set** `{z : ρ·S(z) = 1}`. Combined with the
interlacing geometry (`secular_root_in_gap`, `secular_ground_state`, `secular_neg_above_max`), the
eigenvalues of `diag d − ρ u uᵀ` interlace the diagonal entries `dᵢ` — one in each gap plus one below
the bottom. This is the operator-theoretic heart of the Stage-1 CCM reconstruction: the reconstructed
spectrum (= the secular roots) is a genuine rank-one-perturbed-diagonal eigenvalue problem, and the
bottom eigenvalue's no-margin crossing (`S = 1`) realizes Weil positivity exactly when its *sign* is
right — which is RH. RH-free. Axiom-clean. -/
theorem rankOne_pert_eigenvalue_iff_secular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (z ρ : ℝ) (hpole : ∀ i, d i - z ≠ 0) :
    ((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) - z • (1 : Matrix ι ι ℝ)).det = 0
      ↔ ρ * (∑ i, u i ^ 2 / (d i - z)) = 1 := by
  have hid : (Matrix.diagonal d - ρ • Matrix.vecMulVec u u) - z • (1 : Matrix ι ι ℝ)
      = -(ρ • Matrix.vecMulVec u u - Matrix.diagonal (fun i => d i - z)) := by
    rw [diagonal_sub_smul_one]; abel
  rw [hid, Matrix.det_neg, mul_eq_zero,
      or_iff_right (pow_ne_zero _ (by norm_num : (-1:ℝ) ≠ 0))]
  exact secular_root_iff_weil_det_zero d u z ρ hpole

/-- **The secular operator is real-symmetric (Hermitian) — its spectrum is real.** The
rank-one-perturbed diagonal `diag d − ρ·u uᵀ` is `IsHermitian`: `diag d` is symmetric
(`isHermitian_diagonal`), `u uᵀ` is symmetric (`(u uᵀ)ᵀ = u uᵀ` by commutativity), and Hermitian-ness
is closed under real scaling and subtraction. By the spectral theorem (`Matrix.IsHermitian.eigenvalues`
takes values in `ℝ`), **all eigenvalues are real** — so the secular roots `{z : ρ·S(z) = 1}`
(= these eigenvalues, by `rankOne_pert_eigenvalue_iff_secular`) are all real. This is the finite
shadow of "the reconstructed Stage-1 spectrum lies on the real line": self-adjointness forces reality
unconditionally; what self-adjointness does NOT force is the *positivity* of the bottom eigenvalue
(the no-margin sign) = RH. RH-free. Axiom-clean. -/
theorem rankOne_pert_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).IsHermitian := by
  have h2 : (Matrix.vecMulVec u u).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  exact (Matrix.isHermitian_diagonal d).sub (h2.smul (IsSelfAdjoint.all ρ))

/-- **Trace / first-moment identity for the reconstructed spectrum.**
`Tr(diag d − ρ·u uᵀ) = (∑ᵢ dᵢ) − ρ·‖u‖²` (with `‖u‖² = ∑ᵢ uᵢ²`). Since the trace equals the sum of
eigenvalues and the eigenvalues are exactly the secular roots (`rankOne_pert_eigenvalue_iff_secular`),
this is the **sum rule** `∑(secular roots) = ∑ᵢ dᵢ − ρ·‖u‖²`: the first moment of the reconstructed
Stage-1 spectrum equals the trace of the poles shifted by the rank-one source mass. RH-free.
Axiom-clean. -/
theorem trace_rankOne_pert {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).trace = (∑ i, d i) - ρ * (∑ i, u i ^ 2) := by
  rw [Matrix.trace_sub, Matrix.trace_diagonal, Matrix.trace_smul, Matrix.trace_vecMulVec,
      smul_eq_mul]
  congr 2
  simp only [dotProduct]
  exact Finset.sum_congr rfl (fun i _ => (pow_two (u i)).symm)

open Matrix in
/-- **Determinant / product sum rule for the reconstructed spectrum.** For nonzero poles
(`d i` all nonzero): `det(diag d - rho * u uT) = (prod_i d i) * (1 - rho * sum_i (u i)^2 / d i)`.
The determinant equals the product of eigenvalues, which (by `rankOne_pert_eigenvalue_iff_secular`)
are the secular roots, so this is the product sum rule
`prod(secular roots) = (prod_i d i) * (1 - rho * S(0))`, where `S(0) = sum_i (u i)^2 / d i`. Proof:
`det(diag d - rho u uT) = (-1)^card * det(rho u uT - diag d)` (`Matrix.det_neg`), then
`T3T5SumRule.nomargin_det` (matrix-determinant lemma) with the diagonal resolvent
`u dot (diag d)inv u = sum (u i)^2 / d i` (`inv_eq_right_inv` + `mulVec_diagonal`); the two `(-1)^card`
factors cancel. Together with `trace_rankOne_pert` this gives the first two symmetric functions of the
reconstructed spectrum (sum and product of the secular roots). RH-free. Axiom-clean. -/
theorem det_rankOne_pert {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ)
    (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).det
      = (∏ i, d i) * (1 - ρ * ∑ i, u i ^ 2 / d i) := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have hres : u ⬝ᵥ ((Matrix.diagonal d)⁻¹ *ᵥ u) = ∑ i, u i ^ 2 / d i := by
    have Minv : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.diagonal_mul_diagonal,
          show (fun i => d i * (d i)⁻¹) = (fun _ : ι => (1:ℝ)) from
            funext (fun i => mul_inv_cancel₀ (hd i)), Matrix.diagonal_one]
    rw [Minv]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv, sq]; ring)
  have hneg : Matrix.diagonal d - ρ • Matrix.vecMulVec u u
      = -(ρ • Matrix.vecMulVec u u - Matrix.diagonal d) := by abel
  rw [hneg, Matrix.det_neg, JensenLadder.T3T5SumRule.nomargin_det (Matrix.diagonal d) hdet u ρ,
      Matrix.det_diagonal, hres]
  have hsq : ((-1:ℝ)) ^ Fintype.card ι * (-1) ^ Fintype.card ι = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [← mul_assoc, hsq, one_mul]

open Matrix in
/-- **Second-moment (sum-of-squares) sum rule for the reconstructed spectrum.**
`Tr((diag d − ρ·u uᵀ)²) = ∑ᵢ (d i)² − 2ρ·∑ᵢ d i·(u i)² + ρ²·(∑ᵢ (u i)²)²`.
Since `Tr(A²) = ∑ (eigenvalues)²` and the eigenvalues are the secular roots
(`rankOne_pert_eigenvalue_iff_secular`), this is the **second-moment sum rule**
`∑(secular roots)² = ∑dᵢ² − 2ρ∑dᵢuᵢ² + ρ²(∑uᵢ²)²`. With `trace_rankOne_pert` (§33, first moment) it
pins the *variance/spread* of the reconstructed Stage-1 spectrum. Proof: expand the noncommutative
square `(D − ρR)² = D² − ρ(DR) − ρ(RD) + ρ²R²` (`sub_mul`/`mul_sub`/`smul_mul_assoc`/`mul_smul_comm`/
`smul_sub`/`smul_smul`), then trace-linearity with the pieces `Tr(D²) = ∑dᵢ²`,
`Tr(DR) = Tr(RD) = ∑dᵢuᵢ²` (`trace_mul_comm`, `diagonal_mul`), `Tr(R²) = (∑uᵢ²)²`
(`vecMulVec_mul_vecMulVec`, no `MulOpposite` friction). RH-free. Axiom-clean. -/
theorem trace_sq_rankOne_pert {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ) :
    ((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) ^ 2).trace
      = (∑ i, (d i) ^ 2) - 2 * ρ * (∑ i, d i * (u i) ^ 2) + ρ ^ 2 * (∑ i, (u i) ^ 2) ^ 2 := by
  set D := Matrix.diagonal d with hD
  set R := Matrix.vecMulVec u u with hR
  have hexp : (D - ρ • R) ^ 2 = D * D - ρ • (D * R) - ρ • (R * D) + (ρ * ρ) • (R * R) := by
    rw [sq]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    abel
  rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_smul]
  have hDD : (D * D).trace = ∑ i, (d i) ^ 2 := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    exact Finset.sum_congr rfl (fun i _ => (sq (d i)).symm)
  have hDR : (D * R).trace = ∑ i, d i * (u i) ^ 2 := by
    rw [hD, hR, Matrix.trace]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.vecMulVec_apply, sq])
  have hRD : (R * D).trace = ∑ i, d i * (u i) ^ 2 := by
    rw [Matrix.trace_mul_comm]; exact hDR
  have hRR : (R * R).trace = (∑ i, (u i) ^ 2) ^ 2 := by
    rw [hR, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul]
    have huu : u ⬝ᵥ u = ∑ i, (u i) ^ 2 := by
      simp only [dotProduct]; exact Finset.sum_congr rfl (fun i _ => (sq (u i)).symm)
    rw [huu, ← pow_two]
  rw [hDD, hDR, hRD, hRR]
  simp only [smul_eq_mul]
  ring

/-- **Secular function derivative (Herglotz/Pick structure).** Off the poles, the secular function is
differentiable with `S'(z₀) = ∑ᵢ aᵢ/(dᵢ − z₀)²`: `HasDerivAt (fun z => ∑ᵢ aᵢ/(dᵢ − z))`
`(∑ᵢ aᵢ/(dᵢ − z₀)²) z₀`. Each term `aᵢ/(dᵢ − z)` differentiates by the chain rule
(`HasDerivAt.const_sub`/`.inv`/`.const_mul`) to `aᵢ/(dᵢ − z₀)²`, then `HasDerivAt.sum`. RH-free.
Axiom-clean. -/
theorem secular_hasDerivAt {ι : Type*} [Fintype ι] (a d : ι → ℝ) {z₀ : ℝ}
    (hne : ∀ i, d i - z₀ ≠ 0) :
    HasDerivAt (fun z => ∑ i, a i / (d i - z)) (∑ i, a i / (d i - z₀) ^ 2) z₀ := by
  have term : ∀ i, HasDerivAt (fun z => a i / (d i - z)) (a i / (d i - z₀) ^ 2) z₀ := by
    intro i
    have h := (((hasDerivAt_id z₀).const_sub (d i)).inv (hne i)).const_mul (a i)
    simp only [id_eq] at h
    have hval : a i * (-(-1) / (d i - z₀) ^ 2) = a i / (d i - z₀) ^ 2 := by ring
    rw [hval] at h
    exact h
  have h := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => term i)
  convert h using 1
  funext z
  simp [Finset.sum_apply]

/-- **Secular function is strictly increasing off the poles (positive derivative) — the Herglotz
property.** With positive weights, `S'(z₀) = ∑ᵢ aᵢ/(dᵢ − z₀)² > 0`. This is the analytic form of the
monotonicity `secular_strictMono_off_poles`: a positive sum of squares in the denominators. (Herglotz/
Pick functions — analytic with positive derivative — are the spectral-theoretic backbone of resolvents
`uᵀ(A − z)⁻¹u`; here it certifies that the reconstructed spectrum's secular function rises strictly
across every gap, the analytic engine of the interlacing.) RH-free. Axiom-clean. -/
theorem secular_deriv_pos {ι : Type*} [Fintype ι] [Nonempty ι] (a d : ι → ℝ) {z₀ : ℝ}
    (ha : ∀ i, 0 < a i) (hne : ∀ i, d i - z₀ ≠ 0) :
    0 < ∑ i, a i / (d i - z₀) ^ 2 :=
  Finset.sum_pos (fun i _ => div_pos (ha i) (by have := hne i; positivity)) Finset.univ_nonempty

/-- **Spectrum = secular root set (proper spectral language).** For `z` not a pole, `z` lies in the
algebra spectrum of the secular operator iff `ρ·S(z) = 1`:
`z ∈ spectrum ℝ (diag d − ρ·u uᵀ) ↔ ρ · ∑ᵢ uᵢ²/(dᵢ − z) = 1`. Via `spectrum.mem_iff`
(`z ∈ spectrum ↔ ¬IsUnit (z•1 − A)`), `Matrix.isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`
(`¬IsUnit ↔ det = 0`), and `rankOne_pert_eigenvalue_iff_secular` (after `det_neg`). This states, in the
canonical spectral vocabulary, that the reconstructed Stage-1 spectrum is exactly the secular root set
— and, since the operator is real-symmetric (`rankOne_pert_isHermitian`), that spectrum is real.
RH-free. Axiom-clean. -/
theorem mem_spectrum_iff_secular {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (z ρ : ℝ)
    (hpole : ∀ i, d i - z ≠ 0) :
    z ∈ spectrum ℝ (Matrix.diagonal d - ρ • Matrix.vecMulVec u u)
      ↔ ρ * (∑ i, u i ^ 2 / (d i - z)) = 1 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not,
      show (z • (1 : Matrix ι ι ℝ) - (Matrix.diagonal d - ρ • Matrix.vecMulVec u u))
        = -((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) - z • (1 : Matrix ι ι ℝ)) from by abel,
      Matrix.det_neg, mul_eq_zero, or_iff_right (pow_ne_zero _ (by norm_num : (-1:ℝ) ≠ 0))]
  exact rankOne_pert_eigenvalue_iff_secular d u z ρ hpole

/-- **Resolvent is positive semidefinite below the spectrum.** For `z` strictly below every pole
(`∀ i, z < d i`), the diagonal resolvent `(diag d − z)⁻¹ = diagonal ((dᵢ − z)⁻¹)` is `PosSemidef`
(every entry `(dᵢ − z)⁻¹ > 0`). This is the standard self-adjoint fact "the resolvent is a positive
operator below the spectrum", and the operator-level dual of `secular_neg_above_max` (the secular sum
`S(z) = uᵀ(diag d − z)⁻¹u ≥ 0` for `z` below the bottom pole, since it is a quadratic form of a PSD
matrix). RH-free. Axiom-clean. -/
theorem diagResolvent_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) {z : ℝ}
    (hz : ∀ i, z < d i) :
    (Matrix.diagonal (fun i => (d i - z)⁻¹)).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have : 0 < d i - z := by have := hz i; linarith
  positivity

/-- **Weighted Cauchy–Schwarz** (positive weights `d i`):
`(∑ᵢ uᵢ xᵢ)² ≤ (∑ᵢ uᵢ²/dᵢ) · (∑ᵢ dᵢ xᵢ²)`. Apply `Finset.sum_mul_sq_le_sq_mul_sq` to
`f i = uᵢ/√dᵢ`, `g i = √dᵢ·xᵢ` (so `f·g = uᵢxᵢ`, `f² = uᵢ²/dᵢ`, `g² = dᵢxᵢ²`). This is the analytic
crux of the finite Weil-positivity criterion `finite_weil_psd_of_secular_le_one`. RH-free.
Axiom-clean. -/
theorem weighted_cauchy_schwarz {ι : Type*} [Fintype ι] (d u x : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∑ i, u i * x i) ^ 2 ≤ (∑ i, (u i) ^ 2 / d i) * (∑ i, d i * (x i) ^ 2) := by
  have hsqrt : ∀ i, Real.sqrt (d i) ≠ 0 := fun i => Real.sqrt_ne_zero'.mpr (hd i)
  have e1 : ∀ i, (u i / Real.sqrt (d i)) * (Real.sqrt (d i) * x i) = u i * x i :=
    fun i => by rw [← mul_assoc, div_mul_cancel₀ (u i) (hsqrt i)]
  have e2 : ∀ i, (u i / Real.sqrt (d i)) ^ 2 = (u i) ^ 2 / d i :=
    fun i => by rw [div_pow, Real.sq_sqrt (le_of_lt (hd i))]
  have e3 : ∀ i, (Real.sqrt (d i) * x i) ^ 2 = d i * (x i) ^ 2 :=
    fun i => by rw [mul_pow, Real.sq_sqrt (le_of_lt (hd i))]
  calc (∑ i, u i * x i) ^ 2
      = (∑ i, (u i / Real.sqrt (d i)) * (Real.sqrt (d i) * x i)) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun i _ => (e1 i).symm)
    _ ≤ (∑ i, (u i / Real.sqrt (d i)) ^ 2) * (∑ i, (Real.sqrt (d i) * x i) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, (u i) ^ 2 / d i) * (∑ i, d i * (x i) ^ 2) := by
        rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_congr rfl (fun i _ => e3 i)]

open Matrix in
/-- **Finite Weil-positivity criterion (the finite no-margin).** For positive poles `d i > 0` and
weight `ρ ≥ 0`, if the secular sum is below the threshold `ρ · S(0) ≤ 1` (with `S(0) = ∑ᵢ uᵢ²/dᵢ`),
then the rank-one-downdated diagonal `diag d − ρ·u uᵀ` is **positive semidefinite**.

Proof: the quadratic form is `xᵀ(diag d − ρ u uᵀ)x = ∑ᵢ dᵢxᵢ² − ρ·(∑ᵢ uᵢxᵢ)²`; by
`weighted_cauchy_schwarz`, `(∑uᵢxᵢ)² ≤ S(0)·(∑dᵢxᵢ²)`, so `ρ(∑uᵢxᵢ)² ≤ ρS(0)·(∑dᵢxᵢ²) ≤ ∑dᵢxᵢ²`,
giving the form `≥ 0` (`nlinarith`).

This is the document's **Stage-2 finite no-margin positivity**: the finite Weil form
`QW = ρ u uᵀ − M` (here `M = diag d`) stays positive precisely while the scalar sum rule sits below
`S = 1`. The no-margin / RH is the *limit* `ρS → 1` as the grid `N → ∞` (where `T3T5SumRule.nomargin_threshold`
gives `det QW = 0`); this finite criterion — proven RH-free — is exactly the per-scale positivity that,
held uniformly in the limit, would be Weil positivity. The open residue is whether it survives `N→∞`
(the `hposMetric` hypothesis = RH). RH-free. Axiom-clean. -/
theorem finite_weil_psd_of_secular_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (ρ : ℝ) (hd : ∀ i, 0 < d i) (hρ : 0 ≤ ρ)
    (hS : ρ * (∑ i, (u i) ^ 2 / d i) ≤ 1) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (rankOne_pert_isHermitian d u ρ)
  intro x
  have hsx : (star x : ι → ℝ) = x := by funext i; simp
  rw [hsx]
  have hquad : x ⬝ᵥ ((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) *ᵥ x)
      = (∑ i, d i * (x i) ^ 2) - ρ * (∑ i, u i * x i) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    congr 1
    · simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hquad]
  have hcs := weighted_cauchy_schwarz d u x hd
  have hQ : 0 ≤ ∑ i, d i * (x i) ^ 2 := Finset.sum_nonneg (fun i _ => by have := hd i; positivity)
  nlinarith [hcs, hQ, hS, hρ, mul_nonneg hρ hQ]

open Matrix in
/-- **The Weil quadratic form.** `xᵀ(diag d − ρ·u uᵀ)x = ∑ᵢ dᵢxᵢ² − ρ·(∑ᵢ uᵢxᵢ)²`. RH-free.
Axiom-clean. -/
theorem weil_quadratic_form {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ)
    (x : ι → ℝ) :
    x ⬝ᵥ ((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) *ᵥ x)
      = (∑ i, d i * (x i) ^ 2) - ρ * (∑ i, u i * x i) ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  · simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Failure of finite Weil positivity above the threshold.** If `ρ · S(0) > 1` (poles positive),
then `diag d − ρ·u uᵀ` is **not** positive semidefinite: the witness `xᵢ = uᵢ/dᵢ` gives quadratic
form `S(0) − ρ·S(0)² = S(0)(1 − ρ·S(0)) < 0` (using `S(0) > 0`, forced since `ρS(0) > 1`). RH-free.
Axiom-clean. -/
theorem finite_weil_not_psd_of_secular_gt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (ρ : ℝ) (hd : ∀ i, 0 < d i) (hS : 1 < ρ * (∑ i, (u i) ^ 2 / d i)) :
    ¬ (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosSemidef := by
  intro hpsd
  have hSnn : 0 ≤ ∑ i, (u i) ^ 2 / d i := Finset.sum_nonneg (fun i _ => by have := hd i; positivity)
  have hSpos : 0 < ∑ i, (u i) ^ 2 / d i := by
    rcases eq_or_lt_of_le hSnn with h | h
    · rw [← h, mul_zero] at hS; linarith
    · exact h
  set x : ι → ℝ := fun i => u i / d i with hx
  have hsum1 : (∑ i, d i * (x i) ^ 2) = ∑ i, (u i) ^ 2 / d i :=
    Finset.sum_congr rfl (fun i _ => by rw [hx]; field_simp)
  have hsum2 : (∑ i, u i * x i) = ∑ i, (u i) ^ 2 / d i :=
    Finset.sum_congr rfl (fun i _ => by rw [hx]; field_simp)
  have hge := hpsd.dotProduct_mulVec_nonneg x
  have hsx : (star x : ι → ℝ) = x := by funext i; simp
  rw [hsx, weil_quadratic_form, hsum1, hsum2] at hge
  nlinarith [hge, hSpos, hS]

/-- **Finite Weil positivity ⟺ below the no-margin threshold.** For positive poles and `ρ ≥ 0`:
`diag d − ρ·u uᵀ` is positive semidefinite **iff** `ρ · ∑ᵢ uᵢ²/dᵢ ≤ 1`. This is the *exact* finite
no-margin characterization (combining `finite_weil_psd_of_secular_le_one` and
`finite_weil_not_psd_of_secular_gt_one`): the finite Weil form `QW` is PSD precisely on the closed
threshold region `{ρ·S ≤ 1}`, with the bottom eigenvalue crossing zero exactly at the no-margin
`ρ·S = 1` (= `T3T5SumRule.nomargin_threshold`'s `det QW = 0`). The Riemann Hypothesis is whether this
holds *uniformly as the grid `N → ∞`* — the capstone's `hposMetric`. RH-free. Axiom-clean. -/
theorem finite_weil_psd_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ)
    (hd : ∀ i, 0 < d i) (hρ : 0 ≤ ρ) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosSemidef ↔ ρ * (∑ i, (u i) ^ 2 / d i) ≤ 1 := by
  refine ⟨fun hpsd => ?_, finite_weil_psd_of_secular_le_one d u ρ hd hρ⟩
  by_contra h
  exact finite_weil_not_psd_of_secular_gt_one d u ρ hd (not_le.mp h) hpsd

open Matrix in
/-- **The outer product `u uᵀ` is positive semidefinite.** Its quadratic form is `(∑ᵢ uᵢxᵢ)² ≥ 0`.
RH-free. Axiom-clean. -/
theorem vecMulVec_self_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) :
    (Matrix.vecMulVec u u).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · unfold Matrix.IsHermitian
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  · intro x
    have hsx : (star x : ι → ℝ) = x := by funext i; simp
    rw [hsx]
    have hq : x ⬝ᵥ (Matrix.vecMulVec u u *ᵥ x) = (∑ i, u i * x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hq]; positivity

/-- **Finite Weil positivity is antitone in the coupling `ρ`.** If `diag d − ρ·u uᵀ` is positive
semidefinite and `ρ' ≤ ρ`, then `diag d − ρ'·u uᵀ` is too: writing
`diag d − ρ'·u uᵀ = (diag d − ρ·u uᵀ) + (ρ − ρ')·u uᵀ`, both summands are PSD (the second since
`u uᵀ ⪰ 0` and `ρ − ρ' ≥ 0`), so the sum is PSD. Monotonicity of the no-margin: weakening the rank-one
downdate preserves positivity. RH-free. Axiom-clean. -/
theorem finite_weil_psd_antitone {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ)
    {ρ ρ' : ℝ} (hρ' : ρ' ≤ ρ)
    (h : (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosSemidef) :
    (Matrix.diagonal d - ρ' • Matrix.vecMulVec u u).PosSemidef := by
  have heq : Matrix.diagonal d - ρ' • Matrix.vecMulVec u u
      = (Matrix.diagonal d - ρ • Matrix.vecMulVec u u) + (ρ - ρ') • Matrix.vecMulVec u u := by
    rw [sub_smul]; abel
  rw [heq]
  exact h.add ((vecMulVec_self_posSemidef u).smul (by linarith : (0:ℝ) ≤ ρ - ρ'))

/-- **Critical coupling.** For positive poles, `ρ ≥ 0`, and `S(0) = ∑ᵢ uᵢ²/dᵢ > 0`, finite Weil
positivity holds iff the coupling is below the critical value `ρ_c = 1/S(0)`:
`(diag d − ρ·u uᵀ).PosSemidef ↔ ρ ≤ 1 / S(0)`. This recasts `finite_weil_psd_iff` (`ρ·S ≤ 1`) in the
coupling-threshold form: the finite Weil form is positive exactly up to the **critical coupling**
`ρ_c = 1/S(0)` — the finite analogue of the Aubry–André / BPS critical point `λ = 1` that the corpus
identifies with the no-margin. The Riemann Hypothesis is whether the physical coupling stays at/below
`ρ_c` uniformly as `N → ∞`. RH-free. Axiom-clean. -/
theorem finite_weil_psd_iff_le_critical {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ)
    (ρ : ℝ) (hd : ∀ i, 0 < d i) (hρ : 0 ≤ ρ) (hSpos : 0 < ∑ i, (u i) ^ 2 / d i) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosSemidef
      ↔ ρ ≤ 1 / (∑ i, (u i) ^ 2 / d i) := by
  rw [finite_weil_psd_iff d u ρ hd hρ]
  exact (le_div_iff₀ hSpos).symm

open Matrix in
/-- **Congruence by an invertible matrix preserves positive semidefiniteness (iff).** For `P` with
invertible determinant, `Pᴴ · A · P` is positive semidefinite iff `A` is. (Mathlib provides only the
forward direction `PosSemidef.conjTranspose_mul_mul_same`; the converse follows by conjugating the
hypothesis by `P⁻¹`, since `A = (P⁻¹)ᴴ · (Pᴴ A P) · P⁻¹`.) This is the reduction engine for extending
the diagonal finite Weil-positivity criterion to a **general positive-definite `M`**: by the spectral
theorem `M = Uᴴ · diag(eigenvalues) · U` with `U` unitary (invertible), so
`M − ρ u uᵀ ⪰ 0 ⟺ diag(eigenvalues) − ρ (Uu)(Uu)ᵀ ⪰ 0`, reducing the actual non-diagonal CCM
`M = W_R + P` to the diagonal case already proven (`finite_weil_psd_iff`). RH-free. Axiom-clean. -/
theorem posSemidef_conj_iff {n : Type*} [Fintype n] [DecidableEq n] {P A : Matrix n n ℝ}
    (hP : IsUnit P.det) :
    (Pᴴ * A * P).PosSemidef ↔ A.PosSemidef := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  constructor
  · intro h
    have key : (P⁻¹)ᴴ * (Pᴴ * A * P) * P⁻¹ = A := by
      rw [show (P⁻¹)ᴴ * (Pᴴ * A * P) * P⁻¹ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) by noncomm_ring,
          ← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [← key]
    exact h.conjTranspose_mul_mul_same (P⁻¹)
  · intro h
    exact h.conjTranspose_mul_mul_same P

open Matrix in
/-- **Congruence by an invertible matrix preserves positive *definiteness* (iff).** The strict
analogue of `posSemidef_conj_iff`: for `P` with invertible determinant, `Pᴴ · A · P` is positive
definite iff `A` is. (Mathlib has the forward `PosDef.conjTranspose_mul_mul_same`, which needs
`Function.Injective B.mulVec`; for invertible `P` that injectivity comes from the left inverse
`P⁻¹.mulVec`. The converse conjugates by `P⁻¹`, as in the PSD case.) Together with `posSemidef_conj_iff`
this is the full congruence-invariance of inertia under invertible change of basis — the engine for
reducing the general-`M` finite Weil form to diagonal/identity at every signature level (and the
PD-congruence-iff that was absent from Mathlib). RH-free. Axiom-clean. -/
theorem posDef_conj_iff {n : Type*} [Fintype n] [DecidableEq n] {P A : Matrix n n ℝ}
    (hP : IsUnit P.det) :
    (Pᴴ * A * P).PosDef ↔ A.PosDef := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinvP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hLP : Function.LeftInverse P⁻¹.mulVec P.mulVec := fun x => by
    rw [Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec]
  have hLPinv : Function.LeftInverse P.mulVec P⁻¹.mulVec := fun x => by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  constructor
  · intro h
    have key : (P⁻¹)ᴴ * (Pᴴ * A * P) * P⁻¹ = A := by
      rw [show (P⁻¹)ᴴ * (Pᴴ * A * P) * P⁻¹ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) by noncomm_ring,
          ← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [← key]
    exact h.conjTranspose_mul_mul_same hLPinv.injective
  · intro h
    exact h.conjTranspose_mul_mul_same hLP.injective

open Matrix in
/-- **Block-diagonal positive definiteness (Schur-PD piece iii).** `fromBlocks A 0 0 D` is positive
definite iff both diagonal blocks are: `(fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef`. The
quadratic form splits as `xᵀ·blockDiag·x = (x∘inl)ᵀ A (x∘inl) + (x∘inr)ᵀ D (x∘inr)`
(`fromBlocks_mulVec` + `zero_mulVec` + the `Fintype.sum_sum_type` decomposition of the dot product);
forward via the test vectors `a ⊕ᵥ 0`, `0 ⊕ᵥ b`, backward via "either block-vector is nonzero, both
forms ≥ 0, the nonzero one > 0". Hermiticity by `isHermitian_fromBlocks_iff`. Genuinely **absent from
Mathlib** (`fromBlocks_posDef_iff` unknown; only the determinant Schur identity is present) — flagged
by berry (chat 2522/2523) as the remaining piece (iii) of the PD Schur criterion. With `posDef_conj_iff`
(§53, congruence preserves PD) and Mathlib's LDU `fromBlocks_eq_of_invertible₁₁`, the full PD Schur
complement criterion `fromBlocks A B Bᴴ D ≻ 0 ⟺ A ≻ 0 ∧ (D − Bᴴ A⁻¹ B) ≻ 0` is now assemblable. RH-free.
Axiom-clean. -/
theorem blockDiag_posDef_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (Matrix.fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  have hquad : ∀ x : m ⊕ n → ℝ,
      star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x)
        = star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))
          + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    intro x
    rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.star_apply]
  constructor
  · intro h
    have hH := Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian
    refine ⟨Matrix.PosDef.of_dotProduct_mulVec_pos hH.1 (fun a ha => ?_),
            Matrix.PosDef.of_dotProduct_mulVec_pos hH.2.2.2 (fun b hb => ?_)⟩
    · have hx : (Sum.elim a 0 : m ⊕ n → ℝ) ≠ 0 := by
        intro hc; apply ha; funext i; have := congrFun hc (Sum.inl i); simpa using this
      have := h.dotProduct_mulVec_pos hx
      rwa [hquad, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, dotProduct_zero,
        add_zero] at this
    · have hx : (Sum.elim 0 b : m ⊕ n → ℝ) ≠ 0 := by
        intro hc; apply hb; funext j; have := congrFun hc (Sum.inr j); simpa using this
      have := h.dotProduct_mulVec_pos hx
      rwa [hquad, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, dotProduct_zero,
        zero_add] at this
  · rintro ⟨hA, hD⟩
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_fromBlocks_iff.mpr ⟨hA.isHermitian, by simp, by simp, hD.isHermitian⟩)
      (fun x hx => ?_)
    rw [hquad]
    have hor : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hx (by rw [← Sum.elim_comp_inl_inr x, hc.1, hc.2]; simp)
    rcases hor with hl | hr
    · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hl)
        (hD.posSemidef.dotProduct_mulVec_nonneg _)
    · exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
        (hD.dotProduct_mulVec_pos hr)

open Matrix in
/-- **Block-diagonal positive semidefiniteness (PSD analog of §54).** `fromBlocks A 0 0 D` is positive
*semi*definite iff both diagonal blocks are: `(fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef`.
Same quadratic-form split as `blockDiag_posDef_iff`, but with `≤` (`add_nonneg` backward, no
"some-block-nonzero" case analysis). Built on the named accessors `PosSemidef.dotProduct_mulVec_nonneg`
and the constructor `PosSemidef.of_dotProduct_mulVec_nonneg`. This is the boundary/`det = 0` counterpart
needed for the **no-margin boundary** of the Weil-form cascade (the critical `ρ·uᵀM⁻¹u = 1` case where
the form is PSD-but-singular — the RH-critical seam). RH-free. Axiom-clean. -/
theorem blockDiag_posSemidef_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  have hquad : ∀ x : m ⊕ n → ℝ,
      star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x)
        = star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))
          + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    intro x
    rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.star_apply]
  constructor
  · intro h
    have hH := Matrix.isHermitian_fromBlocks_iff.mp h.1
    refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH.1 (fun a => ?_),
            Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH.2.2.2 (fun b => ?_)⟩
    · have := h.dotProduct_mulVec_nonneg (Sum.elim a 0)
      rwa [hquad, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, dotProduct_zero, add_zero] at this
    · have := h.dotProduct_mulVec_nonneg (Sum.elim 0 b)
      rwa [hquad, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, dotProduct_zero, zero_add] at this
  · rintro ⟨hA, hD⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_fromBlocks_iff.mpr ⟨hA.1, by simp, by simp, hD.1⟩) (fun x => ?_)
    rw [hquad]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

/-- **Finite Weil positivity, identity case.** `1 − ρ·v vᵀ ⪰ 0 ⟺ ρ·‖v‖² ≤ 1` (rank-one downdate of
the identity = the isotropic Weil form). The `d ≡ 1` specialization of `finite_weil_psd_iff`. RH-free.
Axiom-clean. -/
theorem finite_weil_psd_iff_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    ((1 : Matrix ι ι ℝ) - ρ • Matrix.vecMulVec v v).PosSemidef ↔ ρ * (∑ i, (v i) ^ 2) ≤ 1 := by
  have h := finite_weil_psd_iff (fun _ : ι => (1:ℝ)) v ρ (fun _ => one_pos) hρ
  simpa only [Matrix.diagonal_one, div_one] using h

open Matrix in
/-- **Finite Weil positivity for a general positive-definite `M` (Gram form).** If `M = Nᴴ·N` with `N`
invertible (so `M` is an arbitrary positive-definite matrix), then `M − ρ·u uᵀ` is positive
semidefinite iff `ρ · ‖(N⁻¹)ᴴ u‖² ≤ 1`. Here `‖(N⁻¹)ᴴ u‖² = ∑ᵢ ((N⁻¹)ᴴ *ᵥ u)ᵢ² = uᵀ(NᴴN)⁻¹u = uᵀM⁻¹u`,
so this is the no-margin threshold `ρ·uᵀM⁻¹u ≤ 1` for **general `M`** — matching the actual
non-diagonal CCM intersection form `M = W_R + P`.

Proof: conjugate by the invertible `N⁻¹` (`posSemidef_conj_iff`); `(N⁻¹)ᴴ(NᴴN − ρ u uᵀ)N⁻¹ = 1 − ρ v vᵀ`
with `v = (N⁻¹)ᴴ *ᵥ u` (using `mul_vecMulVec`/`vecMulVec_mul` and `u ᵥ* N⁻¹ = (N⁻¹)ᴴ *ᵥ u`), then the
identity case `finite_weil_psd_iff_identity`. No spectral theorem and no matrix square root needed —
just the congruence engine. RH-free. Axiom-clean. -/
theorem finite_weil_psd_iff_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (u : ι → ℝ) (ρ : ℝ) (hN : IsUnit N.det) (hρ : 0 ≤ ρ) :
    (Nᴴ * N - ρ • Matrix.vecMulVec u u).PosSemidef
      ↔ ρ * (∑ i, ((N⁻¹)ᴴ *ᵥ u) i ^ 2) ≤ 1 := by
  have hNN : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have hNinv : IsUnit (N⁻¹).det := by
    have hmul : N⁻¹.det * N.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul N hN, Matrix.det_one]
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hmul)
  have hv : u ᵥ* N⁻¹ = (N⁻¹)ᴴ *ᵥ u := by
    funext j
    simp only [vecMul, mulVec, dotProduct, Matrix.conjTranspose_apply, star_trivial]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hconj : (N⁻¹)ᴴ * (Nᴴ * N - ρ • Matrix.vecMulVec u u) * N⁻¹
      = 1 - ρ • Matrix.vecMulVec ((N⁻¹)ᴴ *ᵥ u) ((N⁻¹)ᴴ *ᵥ u) := by
    have ht1 : (N⁻¹)ᴴ * (Nᴴ * N) * N⁻¹ = 1 := by
      rw [show (N⁻¹)ᴴ * (Nᴴ * N) * N⁻¹ = ((N⁻¹)ᴴ * Nᴴ) * (N * N⁻¹) by noncomm_ring,
          ← Matrix.conjTranspose_mul, hNN, Matrix.conjTranspose_one, Matrix.one_mul]
    have ht2 : (N⁻¹)ᴴ * (ρ • Matrix.vecMulVec u u) * N⁻¹
        = ρ • Matrix.vecMulVec ((N⁻¹)ᴴ *ᵥ u) ((N⁻¹)ᴴ *ᵥ u) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
    rw [Matrix.mul_sub, Matrix.sub_mul, ht1, ht2]
  rw [← posSemidef_conj_iff hNinv, hconj]
  exact finite_weil_psd_iff_identity ((N⁻¹)ᴴ *ᵥ u) ρ hρ

open Matrix in
/-- **Finite Weil positivity for general PD `M`, canonical no-margin form.** For `M = Nᴴ·N` (`N`
invertible — i.e. `M` an arbitrary positive-definite matrix):
`(Nᴴ·N − ρ·u uᵀ).PosSemidef ↔ ρ · (u ⬝ᵥ (Nᴴ·N)⁻¹ *ᵥ u) ≤ 1`,
i.e. `M − ρ·u uᵀ ⪰ 0 ⟺ ρ·uᵀM⁻¹u ≤ 1`. This is the **exact document Stage-2 finite no-margin criterion
for the actual (non-diagonal) CCM intersection form `M = W_R + P`**, in the canonical
`uᵀM⁻¹u` vocabulary — matching `T3T5SumRule.nomargin_threshold` (`det QW = 0 ⟺ ρ·uᵀM⁻¹u = 1`): `QW` is
positive semidefinite precisely up to the no-margin, with the determinant vanishing at it. Derived
from `finite_weil_psd_iff_gram` by the identity `∑ᵢ ((N⁻¹)ᴴ *ᵥ u)ᵢ² = uᵀ(NᴴN)⁻¹u` (`mulVec_mulVec`,
`mul_inv_rev`, `conjTranspose_nonsing_inv`, and `u ᵥ* N⁻¹ = (N⁻¹)ᴴ *ᵥ u` over ℝ). The Riemann
Hypothesis is whether `ρ·uᵀM⁻¹u ≤ 1` holds uniformly as the grid `N → ∞` (the capstone's `hposMetric`).
RH-free. Axiom-clean. -/
theorem finite_weil_psd_iff_gram' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (u : ι → ℝ) (ρ : ℝ) (hN : IsUnit N.det) (hρ : 0 ≤ ρ) :
    (Nᴴ * N - ρ • Matrix.vecMulVec u u).PosSemidef
      ↔ ρ * (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u)) ≤ 1 := by
  have hT : (N⁻¹)ᴴ = (N⁻¹)ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hadj : ∀ w : ι → ℝ, ((N⁻¹)ᴴ *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (N⁻¹ *ᵥ w) := fun w => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hT]
  have hss : (∑ i, ((N⁻¹)ᴴ *ᵥ u) i ^ 2) = ((N⁻¹)ᴴ *ᵥ u) ⬝ᵥ ((N⁻¹)ᴴ *ᵥ u) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun i _ => pow_two _)
  have hsum : (∑ i, ((N⁻¹)ᴴ *ᵥ u) i ^ 2) = u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u) := by
    rw [hss, hadj, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
  rw [finite_weil_psd_iff_gram N u ρ hN hρ, hsum]

/-- **Strict finite Weil positivity (the sharp no-margin trichotomy).** For positive poles and
`ρ ≥ 0`, `diag d − ρ·u uᵀ` is *positive definite* iff the secular sum is **strictly** below the
threshold: `(diag d − ρ·u uᵀ).PosDef ↔ ρ · ∑ᵢ uᵢ²/dᵢ < 1`. Combined with `finite_weil_psd_iff`
(`⪰ 0 ⟺ ρ·S ≤ 1`) and `det_rankOne_pert` (`det = (∏dᵢ)(1 − ρ·S)`, zero exactly at `ρ·S = 1`), this is
the complete trichotomy of the finite Weil form `QW = diag d − ρ·u uᵀ`:
`ρ·S < 1 ⟺ QW ≻ 0` (strict positivity); `ρ·S = 1 ⟺ det QW = 0` (the no-margin boundary, bottom
eigenvalue exactly 0); `ρ·S > 1 ⟺ ¬ QW ⪰ 0` (positivity fails). Proof: `PosDef ⟺ PosSemidef ∧ det ≠ 0`
(`PosSemidef.posDef_iff_det_ne_zero`) with the determinant formula. RH-free. Axiom-clean. -/
theorem finite_weil_posDef_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (d u : ι → ℝ) (ρ : ℝ)
    (hd : ∀ i, 0 < d i) (hρ : 0 ≤ ρ) :
    (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).PosDef ↔ ρ * (∑ i, (u i) ^ 2 / d i) < 1 := by
  have hdne : ∀ i, d i ≠ 0 := fun i => (hd i).ne'
  have hdet : (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).det
      = (∏ i, d i) * (1 - ρ * ∑ i, (u i) ^ 2 / d i) := det_rankOne_pert d u ρ hdne
  have hprod : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hdne i)
  constructor
  · intro hPD
    have hle : ρ * (∑ i, (u i) ^ 2 / d i) ≤ 1 := (finite_weil_psd_iff d u ρ hd hρ).mp hPD.posSemidef
    have hne : (Matrix.diagonal d - ρ • Matrix.vecMulVec u u).det ≠ 0 := hPD.det_pos.ne'
    rw [hdet] at hne
    have h1 : (1 - ρ * ∑ i, (u i) ^ 2 / d i) ≠ 0 := right_ne_zero_of_mul hne
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (by rw [h]; ring : (1 - ρ * ∑ i, (u i) ^ 2 / d i) = 0) h1
  · intro hlt
    have hPSD := finite_weil_psd_of_secular_le_one d u ρ hd hρ (le_of_lt hlt)
    rw [hPSD.posDef_iff_det_ne_zero, hdet]
    exact mul_ne_zero hprod (sub_ne_zero.mpr hlt.ne')

open Matrix in
/-- **Strict finite Weil positivity for general PD `M` (the full no-margin trichotomy, general
operator).** For `M = Nᴴ·N` (`N` invertible) and `ρ ≥ 0`:
`(Nᴴ·N − ρ·u uᵀ).PosDef ↔ ρ · uᵀM⁻¹u < 1`. Combined with `finite_weil_psd_iff_gram'`
(`⪰ 0 ⟺ ρ·uᵀM⁻¹u ≤ 1`) and the determinant `det(M − ρ u uᵀ) = det M · (1 − ρ·uᵀM⁻¹u)`
(`T3T5SumRule.nomargin_det` after `det_neg`), this is the **complete trichotomy for the actual
non-diagonal CCM Weil form** `QW = M − ρ u uᵀ`:
`ρ·uᵀM⁻¹u < 1 ⟺ QW ≻ 0`; `ρ·uᵀM⁻¹u = 1 ⟺ det QW = 0` (no-margin boundary); `ρ·uᵀM⁻¹u > 1 ⟺ ¬ QW ⪰ 0`.
Proof: `PosSemidef.posDef_iff_det_ne_zero` with the determinant formula (`det M = (det N)² ≠ 0`).
RH-free. Axiom-clean. -/
theorem finite_weil_posDef_iff_gram' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (u : ι → ℝ) (ρ : ℝ) (hN : IsUnit N.det) (hρ : 0 ≤ ρ) :
    (Nᴴ * N - ρ • Matrix.vecMulVec u u).PosDef ↔ ρ * (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u)) < 1 := by
  have hMdet : IsUnit ((Nᴴ * N).det) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]; exact hN.star.mul hN
  have hdet : (Nᴴ * N - ρ • Matrix.vecMulVec u u).det
      = (Nᴴ * N).det * (1 - ρ * (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u))) := by
    rw [show Nᴴ * N - ρ • Matrix.vecMulVec u u = -(ρ • Matrix.vecMulVec u u - Nᴴ * N) by abel,
        Matrix.det_neg, JensenLadder.T3T5SumRule.nomargin_det (Nᴴ * N) hMdet u ρ]
    have hsq : ((-1:ℝ)) ^ Fintype.card ι * (-1) ^ Fintype.card ι = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← mul_assoc, hsq, one_mul]
  have hprod : (Nᴴ * N).det ≠ 0 := hMdet.ne_zero
  constructor
  · intro hPD
    have hle := (finite_weil_psd_iff_gram' N u ρ hN hρ).mp hPD.posSemidef
    have hne : (Nᴴ * N - ρ • Matrix.vecMulVec u u).det ≠ 0 := hPD.det_pos.ne'
    rw [hdet] at hne
    have h1 : (1 - ρ * (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u))) ≠ 0 := right_ne_zero_of_mul hne
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (by rw [h]; ring : (1 - ρ * (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u))) = 0) h1
  · intro hlt
    have hPSD := (finite_weil_psd_iff_gram' N u ρ hN hρ).mpr (le_of_lt hlt)
    rw [hPSD.posDef_iff_det_ne_zero, hdet]
    exact mul_ne_zero hprod (sub_ne_zero.mpr hlt.ne')

open Matrix in
/-- **Critical coupling for the general CCM operator.** For `M = Nᴴ·N` (`N` invertible), `ρ ≥ 0`, and
`uᵀM⁻¹u > 0`, the finite Weil form is positive semidefinite iff the coupling stays below the critical
value `ρ_c = 1/(uᵀM⁻¹u)`: `(Nᴴ·N − ρ·u uᵀ).PosSemidef ↔ ρ ≤ 1 / (uᵀ(NᴴN)⁻¹u)`. The general-`M`
analogue of `finite_weil_psd_iff_le_critical` (§43) — the finite Aubry–André / BPS critical point
`λ = 1` for the actual (non-diagonal) CCM operator. RH = whether the physical coupling stays ≤ `ρ_c`
uniformly as `N → ∞`. RH-free. Axiom-clean. -/
theorem finite_weil_psd_iff_gram_le_critical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (u : ι → ℝ) (ρ : ℝ) (hN : IsUnit N.det) (hρ : 0 ≤ ρ)
    (hS : 0 < u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u)) :
    (Nᴴ * N - ρ • Matrix.vecMulVec u u).PosSemidef
      ↔ ρ ≤ 1 / (u ⬝ᵥ ((Nᴴ * N)⁻¹ *ᵥ u)) := by
  rw [finite_weil_psd_iff_gram' N u ρ hN hρ]
  exact (le_div_iff₀ hS).symm

open Matrix in
/-- **The Weil form has at most one negative direction (Lorentzian-dual of the inertia bound).** For
positive-semidefinite `M` and `ρ ≥ 0`, any subspace on which `ρ·u uᵀ − M` is positive definite has
dimension `≤ 1`. Equivalently, the Weil form `QW = M − ρ·u uᵀ` (a rank-one *downdate* of `M`) has at
most one negative eigenvalue: its negative inertia is `≤ 1`. So when per-scale positivity fails
(`ρ·uᵀM⁻¹u > 1`, `finite_weil_posDef_iff_gram'`), it fails **minimally** — a single negative direction,
the no-margin/ample direction. This is the Lorentzian-signature dual of the §16–20 inertia bound
(`psdDiff_finrank_le_one_of_rangeLine` applied to the rank-1 part `ρ·u uᵀ`, whose range is the line
`ℝ ∙ u`), tying the Stage-2 signature `(n−1, 1)` to the no-margin. RH-free. Axiom-clean. -/
theorem weil_neg_inertia_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) (u : ι → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) {W : Submodule ℝ (ι → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < x ⬝ᵥ ((ρ • Matrix.vecMulVec u u - M) *ᵥ x)) :
    Module.finrank ℝ W ≤ 1 := by
  have hrank1 : ∀ x : ι → ℝ, (ρ • Matrix.vecMulVec u u) *ᵥ x = (ρ * (u ⬝ᵥ x)) • u := by
    intro x; funext i
    simp only [mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hr : LinearMap.range (ρ • Matrix.vecMulVec u u).mulVecLin ≤ ℝ ∙ u := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, hrank1 x]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  exact WeilFluctuationLoewner.psdDiff_finrank_le_one_of_rangeLine
    ((vecMulVec_self_posSemidef u).smul hρ) hM hr hW

open Matrix in
/-- **Weil value on the ample/resolvent direction.** On the canonical direction `x = M⁻¹u` (here
`xᵢ = uᵢ/dᵢ` for `M = diag d`), the finite Weil quadratic form takes the value
`(M⁻¹u)ᵀ(diag d − ρ·u uᵀ)(M⁻¹u) = S·(1 − ρ·S)`, where `S = ∑ᵢ uᵢ²/dᵢ = uᵀM⁻¹u`. This is **exactly the
no-margin made explicit**: the value is `> 0` for `ρ·S < 1` (positivity), `= 0` precisely at the
no-margin `ρ·S = 1` (the ample/ground-state direction becomes null — the BPS/critical point), and
`< 0` for `ρ·S > 1` (the single Lorentzian negative direction of `weil_neg_inertia_le_one`). So the
resolvent direction `M⁻¹u` IS the direction that crosses zero at the no-margin. (Holds unconditionally:
where `dᵢ = 0` the term degenerates consistently as `x/0 = 0`.) RH-free. Axiom-clean. -/
theorem weil_value_resolvent_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (ρ : ℝ) :
    (fun i => u i / d i) ⬝ᵥ
        ((Matrix.diagonal d - ρ • Matrix.vecMulVec u u) *ᵥ (fun i => u i / d i))
      = (∑ i, (u i) ^ 2 / d i) * (1 - ρ * (∑ i, (u i) ^ 2 / d i)) := by
  rw [weil_quadratic_form]
  have hsum1 : (∑ i, d i * ((fun i => u i / d i) i) ^ 2) = ∑ i, (u i) ^ 2 / d i :=
    Finset.sum_congr rfl (fun i _ => by simp only; field_simp)
  have hsum2 : (∑ i, u i * ((fun i => u i / d i) i)) = ∑ i, (u i) ^ 2 / d i :=
    Finset.sum_congr rfl (fun i _ => by simp only; field_simp)
  rw [hsum1, hsum2]; ring

open Matrix in
/-- **Explicit Lorentzian positive direction above the no-margin.** When `ρ·S > 1` (`S = ∑ᵢ uᵢ²/dᵢ`),
the line `ℝ ∙ M⁻¹u` (here `M⁻¹u = (uᵢ/dᵢ)`) is a *positive-definite* subspace for the Weil form
`QW = ρ·u uᵀ − diag d`: on `x = c·M⁻¹u`, `x ⬝ᵥ QW *ᵥ x = c²·S·(ρ·S − 1) > 0`. Combined with
`weil_neg_inertia_le_one` (every positive-definite subspace of `QW` has dimension ≤ 1), this pins the
**exact Lorentzian signature `(1, n−1)`** of the Weil form beyond the no-margin: exactly one positive
direction, and it is the ample/resolvent direction `M⁻¹u`. So the Stage-2 "(1, n−1)" signature is fully
concrete — one positive direction, explicitly `M⁻¹u`, appearing precisely when `ρ·S > 1`. RH-free.
Axiom-clean. -/
theorem weil_lorentzian_positive_line {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d u : ι → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hS : 1 < ρ * (∑ i, (u i) ^ 2 / d i)) :
    ∀ x ∈ (ℝ ∙ (fun i => u i / d i)), x ≠ 0 →
      0 < x ⬝ᵥ ((ρ • Matrix.vecMulVec u u - Matrix.diagonal d) *ᵥ x) := by
  intro x hx hxne
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hval : (c • (fun i => u i / d i)) ⬝ᵥ
      ((ρ • Matrix.vecMulVec u u - Matrix.diagonal d) *ᵥ (c • (fun i => u i / d i)))
      = c ^ 2 * ((∑ i, (u i) ^ 2 / d i) * (ρ * (∑ i, (u i) ^ 2 / d i) - 1)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
        show (ρ • Matrix.vecMulVec u u - Matrix.diagonal d)
          = -(Matrix.diagonal d - ρ • Matrix.vecMulVec u u) by abel,
        Matrix.neg_mulVec, dotProduct_neg, weil_value_resolvent_direction]
    ring
  rw [hval]
  have hc : c ≠ 0 := by rintro rfl; simp at hxne
  have hSpos : 0 < ∑ i, (u i) ^ 2 / d i := by
    by_contra hcon; rw [not_lt] at hcon; nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ hcon]
  have hthr : 0 < ρ * (∑ i, (u i) ^ 2 / d i) - 1 := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  exact mul_pos hc2 (mul_pos hSpos hthr)

open Matrix in
/-- **Positive-definite Schur complement criterion (Mathlib gap, fully assembled).** For a real block
matrix `[[A, B], [Bᴴ, D]]` with `A` positive definite, the whole block matrix is positive definite
**iff** the Schur complement `D − Bᴴ A⁻¹ B` is positive definite. Proof = the LDU/congruence of Cohen:
with `U = [[1, A⁻¹B], [0, 1]]` (unit determinant `1`), one has the exact congruence
`[[A, B], [Bᴴ, D]] = Uᴴ · diag(A, D − Bᴴ A⁻¹ B) · U` (Mathlib's `fromBlocks_eq_of_invertible₁₁`, with
the lower factor identified as `Uᴴ` via `(⅟A)ᴴ = ⅟A` for Hermitian `A`). Then `posDef_conj_iff` (§53,
congruence by the invertible `U` preserves positive-definiteness) reduces to the block-diagonal form,
and `blockDiag_posDef_iff` (§54) splits it into `A.PosDef ∧ (Schur).PosDef`; `A.PosDef` is the
hypothesis, leaving the Schur complement as the sole condition. This is the criterion the team's
**incremental-Schur / MonotoneNoMargin** route requires (every Schur-PD step in the Weil-form cascade
is now machine-backed). RH-free. Axiom-clean. -/
theorem schur_posDef_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) (hA : A.PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef ↔ (D - Bᴴ * A⁻¹ * B).PosDef := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAinvH : (⅟A)ᴴ = ⅟A := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.conjTranspose_nonsing_inv, hA.isHermitian.eq]
  set U : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks (1 : Matrix m m ℝ) (⅟A * B) (0 : Matrix n m ℝ) (1 : Matrix n n ℝ) with hUdef
  have hUH : Uᴴ = Matrix.fromBlocks (1 : Matrix m m ℝ) 0 (Bᴴ * ⅟A) 1 := by
    simp only [hUdef, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, hAinvH]
  have hUdet : IsUnit U.det := by
    rw [hUdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
    exact isUnit_one
  have hcong : Matrix.fromBlocks A B Bᴴ D
      = Uᴴ * Matrix.fromBlocks A 0 0 (D - Bᴴ * ⅟A * B) * U := by
    rw [hUH, hUdef, Matrix.fromBlocks_eq_of_invertible₁₁ A B Bᴴ D]
  rw [hcong, posDef_conj_iff hUdet, blockDiag_posDef_iff, Matrix.invOf_eq_nonsing_inv]
  exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩

open Matrix in
/-- **Positive-semidefinite Schur complement criterion (PSD analog of §55).** For a real block matrix
`[[A, B], [Bᴴ, D]]` with `A` **positive definite** (the pivot block must still be strictly positive for
`A⁻¹` to exist), the whole block matrix is positive *semi*definite **iff** the Schur complement
`D − Bᴴ A⁻¹ B` is positive semidefinite. Identical LDU/congruence as `schur_posDef_iff`, threaded
through `posSemidef_conj_iff` (§44) and `blockDiag_posSemidef_iff`; the `A.PosSemidef` conjunct is
discharged by `hA.posSemidef`. This is the criterion that certifies the **no-margin boundary** itself:
at the critical coupling the Weil form is PSD-but-singular, and this iff localizes that singularity to
the Schur complement of the pivot. RH-free. Axiom-clean. -/
theorem schur_posSemidef_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) (hA : A.PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAinvH : (⅟A)ᴴ = ⅟A := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.conjTranspose_nonsing_inv, hA.isHermitian.eq]
  set U : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks (1 : Matrix m m ℝ) (⅟A * B) (0 : Matrix n m ℝ) (1 : Matrix n n ℝ) with hUdef
  have hUH : Uᴴ = Matrix.fromBlocks (1 : Matrix m m ℝ) 0 (Bᴴ * ⅟A) 1 := by
    simp only [hUdef, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, hAinvH]
  have hUdet : IsUnit U.det := by
    rw [hUdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
    exact isUnit_one
  have hcong : Matrix.fromBlocks A B Bᴴ D
      = Uᴴ * Matrix.fromBlocks A 0 0 (D - Bᴴ * ⅟A * B) * U := by
    rw [hUH, hUdef, Matrix.fromBlocks_eq_of_invertible₁₁ A B Bᴴ D]
  rw [hcong, posSemidef_conj_iff hUdet, blockDiag_posSemidef_iff, Matrix.invOf_eq_nonsing_inv]
  exact ⟨fun h => h.2, fun h => ⟨hA.posSemidef, h⟩⟩

/-- **Stage-0 two-piece reduction, made concrete (the faithful integer = the no-margin scalar).**
The Stage-0 deliverable of `program_T3_T5_self_product_construction_20260617.md` (line 46) asks for the
statement that the *faithful boundary integer* gives `κ₋ = 0` and that this, with the measured bulk, is
Weil positivity. `JensenLadder.FaithfulMeasuredDichotomy` formalizes the abstract version (an
inertia-sequence `WeilInertiaSeq`, with `FaithfulPositive` = the off-line count is eventually `0`).
This theorem realizes that abstract faithful-positivity **concretely** for the arithmetic finite Weil
forms: along the prime cutoff `N` (varying source `u N`, coupling `ρ N`, fixed grid `d > 0`), the Weil
downdate `diag d − ρ·u uᵀ` is **eventually positive semidefinite** (the faithful integer is eventually
`0`) **iff** the explicit, root-free **no-margin scalar** `ρ·∑ᵢ uᵢ²/dᵢ = ρ·uᵀ(diag d)⁻¹u` stays
**eventually `≤ 1`**. Pointwise this is `finite_weil_psd_iff`; the `Filter.eventually_congr` lifts it to
the cutoff limit. So the Stage-0 "faithful integer survives the limit" condition is *exactly* "the
no-margin scalar does not cross `1` in the limit" — the computable quantity (berry's prime-axis gate
`ρ·uᵀM⁻¹u`). RH-free: whether the *arithmetic* scalar stays `≤ 1` (the no-margin = De Bruijn–Newman
`Λ = 0`) is the open Stage-5 core, NOT decided here. Axiom-clean. -/
theorem faithful_positive_iff_nomargin_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (u : ℕ → ι → ℝ) (ρ : ℕ → ℝ)
    (hd : ∀ i, 0 < d i) (hρ : ∀ N, 0 ≤ ρ N) :
    (∀ᶠ N in Filter.atTop,
        (Matrix.diagonal d - ρ N • Matrix.vecMulVec (u N) (u N)).PosSemidef)
      ↔ (∀ᶠ N in Filter.atTop, ρ N * (∑ i, (u N i) ^ 2 / d i) ≤ 1) := by
  apply Filter.eventually_congr
  filter_upwards with N
  exact finite_weil_psd_iff d (u N) (ρ N) hd (hρ N)

end SecularGroundState
end JensenLadder
