import JensenLadder.DeterminantHurwitzRoute

/-!
# Genus-one determinant control: the det ↔ eigenvalue bridge (forward half)

The capstone `HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire` consumes
**function-level** convergence (`TendstoLocallyUniformlyOn F xiEntire`). The CCM /
Śliwiński literature works at the **eigenvalue-position** level (zeros of the finite
determinants vs. the ζ zeros). This module isolates the bridge between the two.

**Forward direction (this file, proved).** If entire `Fₙ` converge locally uniformly on
ℂ to an entire `g ≢ 0`, then the zeros of `Fₙ` *accumulate at every zero of* `g`: for each
zero `z₀` of `g` and each `ε > 0`, eventually `Fₙ` has a zero within `ε` of `z₀`. Conversely,
any convergent sequence of finite zeros can only converge to a zero of `g`. Together these are
the no-missing/no-spurious forward consequences of locally-uniform determinant convergence.
The no-missing half uses the zero-detection direction of Hurwitz's theorem (absent from mathlib
as an export), reusing the same argument-principle machinery (`factor_isolated_zero`,
`argprin_isolated`, `tendsto_circleIntegral_logDeriv`, `subLemma1`).

**Reverse direction (open, scoped).** The genuinely load-bearing connective — *zero/eigenvalue
convergence + canonical-product (genus-1) control ⟹ locally-uniform function convergence* —
requires Hadamard factorization / order-of-growth / canonical products, which the pinned
mathlib does **not** provide. That is a separate development (`GenusOneDeterminantControl`,
reverse), not attempted here. It does not discharge `hconv`; both directions leave the
convergence `det_reg → Ξ` (= RH) open.

Evidence class: proved lemma / formal artifact. Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

open Complex Metric Filter Topology

namespace JensenLadder.HurwitzBridge

/-- **Hurwitz zero-detection (forward bridge).** If entire functions `Fₙ` converge locally
uniformly on ℂ to an entire `g` that is not identically zero, then at every zero `z₀` of `g`
the zeros of `Fₙ` accumulate: for every `ε > 0`, eventually `Fₙ` has a zero in the closed
`ε`-ball about `z₀`. -/
theorem zeros_accumulate_at_zero_of_tendstoLocallyUniformly
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hga : AnalyticOnNhd ℂ g Set.univ) (hFa : ∀ n, AnalyticOnNhd ℂ (F n) Set.univ)
    (hconv : TendstoLocallyUniformlyOn F g atTop Set.univ)
    (hg0 : ∃ z, g z ≠ 0) (hz₀ : g z₀ = 0) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∃ z ∈ closedBall z₀ ε, F m z = 0 := by
  -- `z₀` is an isolated zero of `g` (else `g ≡ 0` on the connected set `univ`).
  have hgnz_local : ¬ ∀ᶠ z in 𝓝 z₀, g z = 0 := by
    intro hev
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 := (hev.filter_mono nhdsWithin_le_nhds).frequently
    have hEq : Set.EqOn g 0 Set.univ :=
      hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ z₀) hfreq
    obtain ⟨w, hgw⟩ := hg0; exact hgw (hEq (Set.mem_univ w))
  obtain ⟨n, h, r, hr, hh_an, hh_ne, hfac⟩ :=
    factor_isolated_zero (hga z₀ (Set.mem_univ z₀)) hgnz_local
  -- the zero has positive order
  have hn1 : 1 ≤ n := by
    have hval : g z₀ = (z₀ - z₀) ^ n * h z₀ := hfac z₀ (mem_ball_self hr)
    rw [hz₀, sub_self] at hval
    rcases n with _ | m
    · exfalso; simp only [pow_zero, one_mul] at hval
      exact (hh_ne z₀ (mem_ball_self hr)) hval.symm
    · omega
  intro ε hε
  -- a contour radius `R` with `0 < R < r` and `R ≤ ε`
  set R := min ε r / 2 with hRdef
  have hR : 0 < R := by have := lt_min hε hr; positivity
  have hRr : R < r := by rw [hRdef]; have := min_le_right ε r; linarith
  have hRε : R ≤ ε := by rw [hRdef]; have := min_le_left ε r; linarith
  have hcb_ball : closedBall z₀ R ⊆ ball z₀ r := fun z hz => by
    rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hsph_ball : sphere z₀ R ⊆ ball z₀ r := fun z hz => hcb_ball (sphere_subset_closedBall hz)
  -- `g ≠ 0` on the contour
  have hgne_sphere : ∀ z ∈ sphere z₀ R, g z ≠ 0 := by
    intro z hz
    rw [hfac z (hsph_ball hz)]
    have hz_ne : z - z₀ ≠ 0 := by
      rw [sub_ne_zero]; intro he; rw [he, mem_sphere, dist_self] at hz; linarith
    exact mul_ne_zero (pow_ne_zero n hz_ne) (hh_ne z (hsph_ball hz))
  -- the argument-principle value of the limit integral is `2πi·n ≠ 0`
  have hint_g : (∮ z in C(z₀, R), logDeriv g z) = 2 * (Real.pi : ℂ) * I * (n : ℂ) :=
    argprin_isolated hR hRr hh_an hh_ne hfac
  have hLne : (2 * (Real.pi : ℂ) * I * (n : ℂ)) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnez : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hnez
  -- the finite-determinant integrals converge to that nonzero value
  have htends :=
    tendsto_circleIntegral_logDeriv isOpen_univ hR (fun _ _ => Set.mem_univ _)
      hga hFa hconv hgne_sphere
  rw [hint_g] at htends
  have hev_ne : ∀ᶠ m in atTop, (∮ z in C(z₀, R), logDeriv (F m) z) ≠ 0 :=
    htends.eventually_ne hLne
  -- a nonzero contour integral forces a zero inside (else `subLemma1` gives `0`)
  filter_upwards [hev_ne] with m hm
  by_contra hcon
  push Not at hcon
  have hFne_cb : ∀ z ∈ closedBall z₀ R, F m z ≠ 0 := fun z hz =>
    hcon z (closedBall_subset_closedBall hRε hz)
  have hint0 : (∮ z in C(z₀, R), logDeriv (F m) z) = 0 :=
    subLemma1 hR.le (subset_refl _) ((hFa m).mono (Set.subset_univ _)) hFne_cb
  exact hm hint0

end JensenLadder.HurwitzBridge

namespace JensenLadder.DeterminantHurwitzRoute
namespace DeterminantApproximants
namespace EigenvalueProductBridge

/--
Canonical-product control has a concrete spectral consequence: every regular
`Ξ` zero is eventually shadowed by finite real eigenheights.

This is the forward Hurwitz direction specialized to the determinant/eigenvalue
dictionary.  It is not the missing reverse theorem; it only says that any
proposed genus-one product-control proof must also supply this no-missing-zero
spectral behavior.
-/
theorem eigenheights_accumulate_at_regularXiZero
    {D : DeterminantApproximants.{u}} {scale : ℕ → D.Scale}
    (B : EigenvalueProductBridge D scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hcontrol : B.canonicalProductControl)
    {z₀ : ℂ} (hz₀ : RHReduction.riemannXiRegularZero z₀) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∃ γ : B.EigenLabel (scale n),
        (B.eigenHeight (scale n) γ : ℂ) ∈ closedBall z₀ ε := by
  intro ε hε
  have hzero : HurwitzBridge.xiEntire z₀ = 0 :=
    xiEntire_eq_zero_of_riemannXiRegularZero hz₀
  have hacc :
      ∀ᶠ n in atTop, ∃ z ∈ closedBall z₀ ε,
        D.determinant (scale n) z = 0 :=
    HurwitzBridge.zeros_accumulate_at_zero_of_tendstoLocallyUniformly
      xiEntire_analyticOnNhd_univ hFa
      (B.locallyUniformToXi_of_canonicalProductControl hcontrol)
      xiEntire_nontrivial hzero ε hε
  filter_upwards [hacc] with n hn
  rcases hn with ⟨z, hzball, hzdet⟩
  rcases B.zero_complete (scale n) z hzdet with ⟨γ, hzγ⟩
  refine ⟨γ, ?_⟩
  simpa [hzγ] using hzball

/--
If a proposed finite determinant spectrum eventually leaves a regular `Ξ` zero
outside every finite eigenheight closed ball at some positive radius, then the
genus-one canonical-product control row cannot hold.
-/
theorem not_canonicalProductControl_of_eventually_missing_regularXiZero
    {D : DeterminantApproximants.{u}} {scale : ℕ → D.Scale}
    (B : EigenvalueProductBridge D scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    {z₀ : ℂ} (hz₀ : RHReduction.riemannXiRegularZero z₀)
    (hmiss : ∃ ε > 0, ∀ᶠ n in atTop,
      ∀ γ : B.EigenLabel (scale n),
        (B.eigenHeight (scale n) γ : ℂ) ∉ closedBall z₀ ε) :
    ¬ B.canonicalProductControl := by
  intro hcontrol
  rcases hmiss with ⟨ε, hε, hmiss_eventually⟩
  have hhit :=
    eigenheights_accumulate_at_regularXiZero B hFa hcontrol hz₀ ε hε
  rw [eventually_atTop] at hhit hmiss_eventually
  rcases hhit with ⟨Nhit, hhit_after⟩
  rcases hmiss_eventually with ⟨Nmiss, hmiss_after⟩
  let n := max Nhit Nmiss
  have hhit_n := hhit_after n (le_max_left Nhit Nmiss)
  have hmiss_n := hmiss_after n (le_max_right Nhit Nmiss)
  rcases hhit_n with ⟨γ, hγball⟩
  exact hmiss_n γ hγball

/--
Canonical-product control also excludes spurious spectral limits: any sequence
of exact finite eigenheight zeros that converges in `ℂ` can only converge to a
zero of the pole-cancelled `Ξ` endpoint.

This deliberately stops at `xiEntire z₀ = 0`.  Upgrading that endpoint to the
regular raw-`Ξ` predicate needs the separate Gamma/pole side conditions.
-/
theorem xiEntire_eq_zero_of_tendsto_eigenheight
    {D : DeterminantApproximants.{u}} {scale : ℕ → D.Scale}
    (B : EigenvalueProductBridge D scale)
    (hcontrol : B.canonicalProductControl)
    {γ : ∀ n : ℕ, B.EigenLabel (scale n)} {z₀ : ℂ}
    (hγ : Tendsto (fun n : ℕ => (B.eigenHeight (scale n) (γ n) : ℂ))
      atTop (𝓝 z₀)) :
    HurwitzBridge.xiEntire z₀ = 0 := by
  have hγ_within :
      Tendsto (fun n : ℕ => (B.eigenHeight (scale n) (γ n) : ℂ))
        atTop (𝓝[Set.univ] z₀) := by
    simpa using hγ
  have hcomp :
      Tendsto
        (fun n : ℕ =>
          D.determinant (scale n) (B.eigenHeight (scale n) (γ n) : ℂ))
        atTop (𝓝 (HurwitzBridge.xiEntire z₀)) :=
    (B.locallyUniformToXi_of_canonicalProductControl hcontrol).tendsto_comp
      HurwitzBridge.xiEntire_differentiable.continuous.continuousWithinAt
      (Set.mem_univ z₀) hγ_within
  have hzero :
      Tendsto
        (fun n : ℕ =>
          D.determinant (scale n) (B.eigenHeight (scale n) (γ n) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
    simp [B.eigen_zero]
  exact (tendsto_nhds_unique hzero hcomp).symm

/--
A convergent finite-eigenheight branch whose limit is not a zero of `xiEntire`
refutes the canonical-product control row.
-/
theorem not_canonicalProductControl_of_tendsto_eigenheight_to_xiEntire_nonzero
    {D : DeterminantApproximants.{u}} {scale : ℕ → D.Scale}
    (B : EigenvalueProductBridge D scale)
    {γ : ∀ n : ℕ, B.EigenLabel (scale n)} {z₀ : ℂ}
    (hγ : Tendsto (fun n : ℕ => (B.eigenHeight (scale n) (γ n) : ℂ))
      atTop (𝓝 z₀))
    (hXi_ne : HurwitzBridge.xiEntire z₀ ≠ 0) :
    ¬ B.canonicalProductControl := by
  intro hcontrol
  exact hXi_ne (B.xiEntire_eq_zero_of_tendsto_eigenheight hcontrol hγ)

end EigenvalueProductBridge
end DeterminantApproximants
end JensenLadder.DeterminantHurwitzRoute
