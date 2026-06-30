import Mathlib

/-!
# Off-line Li detector: the quadratic off-line response (RH-content side)

The steer "the easy linear/unitary invariant is blind; RH lives in the quadratic/spectral-identification
piece" directs the search to the *quadratic* response. In berry's Li–Cayley picture
(`LiCayleyAtom`), a zero `ρ` maps to `w = 1 − 1/ρ`, the FE acting as `w ↦ 1/w`, so zeros sit in quartets
`{w, w̄, 1/w, 1/w̄}`; the quartet's contribution to the Li coefficient `λ_n = Σ_ρ (1 − w_ρⁿ)` is
`g(n) = 4 − 2 cos(nα)(rⁿ + r⁻ⁿ)` where `w = r e^{iα}`. On-line (`r = 1`) this is `≥ 0` for all `n`
(berry's `li_pair_nonneg`); **off-line** (`r ≠ 1`) it oscillates to `−∞`.

This module proves the **off-line detector core**: for `r > 1`, `g(n)` is **unbounded below**. The auxiliary
theorem `cos_half_recurrence` discharges the Diophantine recurrence `cos(nα) ≥ 1/2` for arbitrarily large
`n` using an `AddCircle` near-return, and `offline_li_unbounded_below_uncond` applies it to every phase. So:

* on-line ⟹ per-quartet Li positivity (berry, proved), and
* off-line ⟹ per-quartet Li contribution unbounded below (here, unconditional),

are the two halves of the per-quartet Li dichotomy. This is the *quadratic / RH-content* side (a single
off-line zero forces Li coefficients negative), complementary to the blind linear/unitary invariant.

**Open (named, not faked):** the full-sum detector — that the off-line quartet's growth dominates the
bounded on-line sum and the other quartets at some `n`, yielding `λ_n < 0` (needs the dominant-`r` argument
+ equidistribution). RH-free.
-/

open Real

namespace JensenLadder

/-- **Analytic core of the recurrence:** if `x` is within `π/3` of an integer multiple of `2π`, then
`cos x ≥ 1/2`. Step toward discharging the Diophantine-recurrence hypothesis of the detector below
(the remaining piece being the near-return `∃ d ≥ 1, dα` near a multiple of `2π`, by Dirichlet). -/
theorem cos_ge_half_of_near_multiple (x β : ℝ) (k : ℤ)
    (hx : x = β + k * (2 * Real.pi)) (hβ : |β| ≤ Real.pi / 3) :
    (1 / 2 : ℝ) ≤ Real.cos x := by
  have hcos : Real.cos x = Real.cos β := by
    rw [hx, Real.cos_add_int_mul_two_pi]
  rw [hcos, abs_le] at *
  have hpi := Real.pi_pos
  have hmono : Real.cos (Real.pi / 3) ≤ Real.cos β := by
    rcases le_total 0 β with hb | hb
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hb (by linarith) hβ.2
    · rw [← Real.cos_neg β]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith [hβ.1])
  rwa [Real.cos_pi_div_three] at hmono

/-- **Diophantine recurrence (Dirichlet).** For every `α` and `N`, there is `n ≥ N` with
`cos(nα) ≥ 1/2`. Via `AddCircle.exists_norm_nsmul_le` (near-return at scale `6N`), then the multiple `N·d`
stays within `π/3` of a multiple of `2π`. This discharges the off-line detector's recurrence hypothesis,
making it unconditional. RH-free. -/
theorem cos_half_recurrence (α : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (1 / 2 : ℝ) ≤ Real.cos (n * α) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨0, le_refl 0, ?_⟩
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero]; norm_num
  · haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    obtain ⟨d, hd_mem, hd_norm⟩ :=
      AddCircle.exists_norm_nsmul_le (↑α : AddCircle (2 * Real.pi)) (n := 6 * N) (by omega)
    have hd1 : 1 ≤ d := hd_mem.1
    refine ⟨N * d, le_mul_of_one_le_right (Nat.zero_le N) hd1, ?_⟩
    set x : ℝ := (↑(N * d) : ℝ) * α with hx
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hnorm : ‖(↑x : AddCircle (2 * Real.pi))‖ ≤ Real.pi / 3 := by
      have hcoe : (↑x : AddCircle (2 * Real.pi)) = (N * d) • (↑α : AddCircle (2 * Real.pi)) := by
        rw [hx, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
      rw [hcoe, mul_smul]
      have hcast : ((6 * N + 1 : ℕ) : ℝ) = 6 * (N : ℝ) + 1 := by push_cast; ring
      have hd_norm' : ‖d • (↑α : AddCircle (2 * Real.pi))‖ ≤ 2 * Real.pi / (6 * (N : ℝ) + 1) := by
        rw [← hcast]; exact hd_norm
      have hstep : 2 * Real.pi / (6 * (N : ℝ) + 1) ≤ 2 * Real.pi / (6 * (N : ℝ)) := by
        gcongr
        linarith
      have heq : (N : ℝ) * (2 * Real.pi / (6 * (N : ℝ))) = Real.pi / 3 := by
        field_simp
        ring
      calc ‖N • (d • (↑α : AddCircle (2 * Real.pi)))‖
          ≤ (N : ℝ) * ‖d • (↑α : AddCircle (2 * Real.pi))‖ := norm_nsmul_le
        _ ≤ (N : ℝ) * (2 * Real.pi / (6 * (N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hd_norm' (le_of_lt hNpos)
        _ ≤ (N : ℝ) * (2 * Real.pi / (6 * (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep (le_of_lt hNpos)
        _ = Real.pi / 3 := heq
    rw [AddCircle.norm_eq] at hnorm
    exact cos_ge_half_of_near_multiple x
      (x - (↑(round ((2 * Real.pi)⁻¹ * x)) : ℝ) * (2 * Real.pi))
      (round ((2 * Real.pi)⁻¹ * x)) (by ring) hnorm

/-- **Off-line detector core (quadratic off-line response).** For an off-line FE-quartet `|w| = r > 1`,
the Li-coefficient contribution `g(n) = 4 − 2 cos(nα)(rⁿ + r⁻ⁿ)` is **unbounded below**, given the
Diophantine recurrence `∀ N, ∃ n ≥ N, cos(nα) ≥ 1/2`. Mechanism: when `cos(nα) ≥ 1/2`, `g(n) ≤ 4 − rⁿ`,
and `rⁿ → ∞`. So an off-line zero forces the Li contribution negative — the RH-content (quadratic) side.
RH-free; the recurrence (true for all `α` by Dirichlet) is isolated as a hypothesis. -/
theorem offline_li_unbounded_below
    (r α : ℝ) (hr : 1 < r)
    (hrec : ∀ N : ℕ, ∃ n, N ≤ n ∧ (1/2 : ℝ) ≤ Real.cos (n * α)) :
    ∀ C : ℝ, ∃ n : ℕ, 4 - 2 * Real.cos (n * α) * (r ^ n + (r ^ n)⁻¹) < C := by
  intro C
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max 0 (4 - C)) hr
  obtain ⟨n, hnN, hcos⟩ := hrec N
  refine ⟨n, ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  have hrn_ge : r ^ N ≤ r ^ n := pow_le_pow_right₀ (le_of_lt hr) hnN
  have h1 : (1 : ℝ) ≤ 2 * Real.cos (n * α) := by linarith
  have h2 : r ^ n ≤ r ^ n + (r ^ n)⁻¹ :=
    le_add_of_nonneg_right (le_of_lt (inv_pos.mpr hrn_pos))
  have hge : r ^ n ≤ 2 * Real.cos (n * α) * (r ^ n + (r ^ n)⁻¹) := by
    calc r ^ n = 1 * r ^ n := (one_mul _).symm
      _ ≤ (2 * Real.cos (n * α)) * (r ^ n + (r ^ n)⁻¹) :=
          mul_le_mul h1 h2 (le_of_lt hrn_pos) (by linarith)
  have hrnC : 4 - C < r ^ n :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN hrn_ge)
  linarith

/-- **Off-line detector (unconditional).** For an off-line FE-quartet `|w| = r > 1` and ANY phase `α`, the
Li-coefficient contribution `g(n) = 4 − 2 cos(nα)(rⁿ + r⁻ⁿ)` is unbounded below — the Diophantine
recurrence hypothesis is now discharged by `cos_half_recurrence`. So an off-line zero forces the Li
contribution arbitrarily negative, for every phase. The quadratic off-line response, fully formal. RH-free
(per-quartet; the full-sum dominance over the on-line terms remains, as noted in the module header). -/
theorem offline_li_unbounded_below_uncond (r α : ℝ) (hr : 1 < r) :
    ∀ C : ℝ, ∃ n : ℕ, 4 - 2 * Real.cos (n * α) * (r ^ n + (r ^ n)⁻¹) < C :=
  offline_li_unbounded_below r α hr (cos_half_recurrence α)

end JensenLadder
