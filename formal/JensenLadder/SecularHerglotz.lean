import Mathlib

/-!
# The secular m-function is Herglotz (positive residues) — the de Branges / continuation structure

Two steers (2026-06-18) relocate the RH wall into a precise method-class:
* the user's *"ζ's RH is a continuation phenomenon, not a convergence/rigidity one"*, and
* berry's meta-pruning from the **proven** Rodgers–Tao `Λ ≥ 0`: since `λ_min(Weil form) → 0`, every
  *margin-based* positivity tool (diagonal-dominance / Gershgorin / trace–Rayleigh / gapped-comparison) is
  FALSE for it; the proof must be **boundary/critical** — Hermite–Biehler / de Branges / Laguerre–Pólya.

The secular Cauchy function `S(z) = ∑ uₙ/(dₙ − z)` is the Weyl–Titchmarsh **m-function** of a canonical
system — the de Branges *continuation* object (a resolvent, not a convergent series). Its defining
structural property in that class is **Herglotz/Nevanlinna**: it maps the upper half-plane into itself.
This module proves that from a pure *sign* condition on the residues — **margin-free**, hence in exactly
the surviving class (not the pruned margin class).

`secular_herglotz`: `uₙ > 0` ⟹ `Im z > 0 ⟹ Im S(z) > 0`. Each term contributes
`Im(uₙ/(dₙ−z)) = uₙ·Im z / |dₙ−z|² > 0`; summing keeps it positive. RH-free.

The forced open target (correctly typed by the two steers): RH ⟺ the *limiting* secular m-function
`S_∞(z) = ∫ dμ(t)/(t−z)` is Herglotz with a **positive measure μ** (de Branges Hamiltonian positivity),
established at the boundary `λ_min = 0` — not via a margin.

**Scope caveat.** `secular_herglotz`/`secular_no_upper_root` require *positive* residues `uₙ > 0`.
The ζ-facing secular reconstruction does not have that sign pattern: its `Q_W` ground-state source alternates
and the structural parity `uₙ=u₋ₙ` with odd grid `dₙ` makes `dₙuₙ` mixed-sign. The prime blocks are non-local
shifts rather than Perron–Frobenius positive kernels. So these two lemmas are a positive-residue **model**;
the ζ-facing object is the **indefinite Hermite–Biehler** case (real spectrum *despite* prime-induced
alternation = RH). The abstract
`herglotz_real_level` / `herglotz_limit_im_nonneg` below remain valid for the canonical-system m-function
(spectral measure = the zero set), and `cauchy_pole_not_herglotz` supplies the one-atom off-line obstruction.
-/

open Complex BigOperators

namespace JensenLadder

/-- **Secular m-function is Herglotz (positive residues).** The secular Cauchy/Weyl–Titchmarsh function
`S(z) = ∑ uₙ/(dₙ − z)` with positive residues `uₙ > 0` and real poles `dₙ` maps the upper half-plane into
itself: `Im z > 0 ⟹ Im S(z) > 0`. This is the de Branges / canonical-system positivity — a *sign*
property of the continuation object, immune to `λ_min → 0` (margin-free, the forced class). RH-free. -/
theorem secular_herglotz {ι : Type*} [Fintype ι] [Nonempty ι] (u d : ι → ℝ)
    (hu : ∀ i, 0 < u i) (z : ℂ) (hz : 0 < z.im) (hd : ∀ i, (d i : ℂ) - z ≠ 0) :
    0 < (∑ i, (u i : ℂ) / ((d i : ℂ) - z)).im := by
  have key : ∀ i : ι, 0 < ((u i : ℂ) / ((d i : ℂ) - z)).im := by
    intro i
    have hw : (d i : ℂ) - z ≠ 0 := hd i
    have hns : 0 < Complex.normSq ((d i : ℂ) - z) := Complex.normSq_pos.mpr hw
    rw [Complex.div_im]
    have e3 : ((d i : ℂ) - z).im = - z.im := by simp [Complex.sub_im, Complex.ofReal_im]
    rw [Complex.ofReal_im, Complex.ofReal_re, e3]
    have hrw : (0 : ℝ) * ((d i : ℂ) - z).re / Complex.normSq ((d i : ℂ) - z)
        - u i * (-z.im) / Complex.normSq ((d i : ℂ) - z)
        = u i * z.im / Complex.normSq ((d i : ℂ) - z) := by ring
    rw [hrw]
    exact div_pos (mul_pos (hu i) hz) hns
  rw [Complex.im_sum]
  exact Finset.sum_pos (fun i _ => key i) Finset.univ_nonempty

/-- **Herglotz ⟹ real spectrum (de Branges real-rootedness, margin-free).** Because the secular
m-function maps the upper half-plane to itself (`secular_herglotz`), the secular equation `S(z) = c` for
any *real* `c` (in particular the ground-state equation `S(z) = 1`) has **no solution with `Im z > 0`**:
a solution would give `0 < Im S(z) = Im c = 0`. By conjugate symmetry the lower half-plane is likewise
free, so every secular eigenvalue is real. This derives real-rootedness from the Herglotz/Nevanlinna
*structure* (the de Branges mechanism), not from any positivity margin — the forced class. RH-free. -/
theorem secular_no_upper_root {ι : Type*} [Fintype ι] [Nonempty ι] (u d : ι → ℝ)
    (hu : ∀ i, 0 < u i) (c : ℝ) (z : ℂ) (hz : 0 < z.im) (hd : ∀ i, (d i : ℂ) - z ≠ 0) :
    (∑ i, (u i : ℂ) / ((d i : ℂ) - z)) ≠ (c : ℂ) := by
  intro h
  have hpos := secular_herglotz u d hu z hz hd
  rw [h, Complex.ofReal_im] at hpos
  exact lt_irrefl _ hpos

/-- **Herglotz ⟹ real level sets (the general de Branges mechanism).** If `g` maps the open upper
half-plane into itself (`Im z > 0 ⟹ Im (g z) > 0`), then for every real `c`, `g z = c` has no solution
with `Im z > 0`. This is `secular_no_upper_root` abstracted to *any* Herglotz function — in particular it
applies to the **limiting** secular m-function `S_∞` once it is known Herglotz, yielding real spectrum
(= RH). General, margin-free, RH-free. -/
theorem herglotz_real_level {g : ℂ → ℂ} (hg : ∀ z, 0 < z.im → 0 < (g z).im)
    (c : ℝ) (z : ℂ) (hz : 0 < z.im) : g z ≠ (c : ℂ) := by
  intro h
  have hpos := hg z hz
  rw [h, Complex.ofReal_im] at hpos
  exact lt_irrefl _ hpos

/-- **Limit of Herglotz values has `Im ≥ 0` (the margin-free continuation transfer).** If the values
`f n` all have positive imaginary part and converge to `L`, then `Im L ≥ 0`. This carries the finite
Herglotz positivity (`secular_herglotz`) to the limiting m-function `S_∞` — the de Branges-class analog of
the Hurwitz / Laguerre–Pólya transfer, immune to `λ_min → 0`. (The remaining wall is upgrading `Im ≥ 0` to
genuine Herglotz with a *positive* measure — de Branges Hamiltonian positivity at the boundary.) RH-free. -/
theorem herglotz_limit_im_nonneg {f : ℕ → ℂ} {L : ℂ}
    (hpos : ∀ n, 0 < (f n).im) (hconv : Filter.Tendsto f Filter.atTop (nhds L)) :
    0 ≤ L.im := by
  have h2 : Filter.Tendsto (fun n => (f n).im) Filter.atTop (nhds L.im) :=
    (Complex.continuous_im.tendsto L).comp hconv
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h2 (fun n => le_of_lt (hpos n))

/-- **Off-line atom breaks Herglotz (the falsification side, the DH mechanism).** A positive point mass
`c > 0` at a *non-real* point `z₀` (`Im z₀ > 0`) makes the Cauchy transform `w ↦ c/(z₀ − w)` fail Herglotz:
there is `w` in the upper half-plane with `Im(c/(z₀ − w)) < 0`. This is the abstract reason an off-line zero
(a complex atom of the limiting measure `Σ_ρ δ_γ`) drives the renormalized form indefinite — the DH side of
the verified ζ/DH inertia discriminator (`hawking_continuation_debranges_synthesis_20260618.md`). Together
with `herglotz_real_level`/`secular_herglotz` it gives the de Branges dichotomy: real atoms ⟹ Herglotz/PSD,
off-line atom ⟹ non-Herglotz/indefinite. RH-free. -/
theorem cauchy_pole_not_herglotz (c : ℝ) (hc : 0 < c) (z₀ : ℂ) (hz : 0 < z₀.im) :
    ∃ w : ℂ, 0 < w.im ∧ ((c : ℂ) / (z₀ - w)).im < 0 := by
  set r : ℝ := z₀.im / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  refine ⟨z₀ - Complex.I * (r : ℂ), ?_, ?_⟩
  · have hw : (z₀ - Complex.I * (r : ℂ)).im = z₀.im - r := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hw, hr]; linarith
  · have hζ : z₀ - (z₀ - Complex.I * (r : ℂ)) = Complex.I * (r : ℂ) := by ring
    rw [hζ]
    have hre : (Complex.I * (r : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have him : (Complex.I * (r : ℂ)).im = r := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have hns : Complex.normSq (Complex.I * (r : ℂ)) = r ^ 2 := by
      rw [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]; ring
    have hval : ((c : ℂ) / (Complex.I * (r : ℂ))).im = -(c / r) := by
      rw [Complex.div_im, hre, him, hns, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      ring
    rw [hval]
    have : 0 < c / r := div_pos hc hrpos
    linarith

end JensenLadder
