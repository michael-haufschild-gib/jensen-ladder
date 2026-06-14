import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Reduction of mathlib's `RiemannHypothesis` to the completed-zeta endpoint

This module is the first *unconditional, kernel-checked* brick of the analytical
route.  It connects the program's working endpoint — statements about the
completed Riemann zeta function `Λ = completedRiemannZeta` — to mathlib's
official statement `RiemannHypothesis`.

mathlib defines (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`)

```text
RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2.
```

The completed zeta factors as `riemannZeta s = Λ s / Gammaℝ s` for `s ≠ 0`
(`riemannZeta_def_of_ne_zero`), where `Gammaℝ s = π^(-s/2) Γ(s/2)` vanishes
*exactly* on `{0, -2, -4, …}` (`Gammaℝ_eq_zero_iff`).  Those are precisely the
points excluded from the RH quantifier (the trivial zeros, together with `s = 0`
where `ζ(0) = -1/2 ≠ 0`).  Hence at every point in scope of the RH quantifier
`Gammaℝ s ≠ 0`, so a zero of `ζ` there is a zero of `Λ`.

**Therefore: if every zero of `Λ` lies on the critical line, then RH holds.**
This is the direction the Jensen / Laguerre–Pólya analysis must deliver.

## Honest scope

This is *not* an RH proof.  It relocates the goal from `riemannZeta` to the
regular zero set of `completedRiemannZeta`, with the Gamma-factor exceptional
set and the pole point filtered out.  The unfiltered "all `Λ` zeros" theorem is
a convenient sufficient condition; the exact RH-equivalent endpoint is
`riemannHypothesis_iff_completedZeta_regular_zeros_on_line` below.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace RHReduction

open Complex

/-- **Brick 1 (ζ ⇐ Λ zero correspondence).**
If every zero of the completed Riemann zeta function `Λ = completedRiemannZeta`
has real part `1/2`, then the Riemann Hypothesis (mathlib's `RiemannHypothesis`)
holds.

The proof is the elementary archimedean-factor bookkeeping: in the scope of the
RH quantifier `s ∉ {0, -2, -4, …}`, so `Gammaℝ s ≠ 0`, and `ζ = Λ / Gammaℝ`
forces `Λ s = 0`. -/
theorem riemannHypothesis_of_completedZeta_zeros_on_line
    (H : ∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hs htriv _hne1
  -- `s ≠ 0`, since `ζ(0) = -1/2 ≠ 0`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  -- `Gammaℝ s ≠ 0`: its zeros are `{0, -2, -4, …}`, all excluded here.
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ m =>
        exact htriv ⟨m, by push_cast at hn ⊢; linear_combination hn⟩
  -- `ζ = Λ / Gammaℝ` with `Gammaℝ s ≠ 0` and `ζ s = 0` forces `Λ s = 0`.
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right hG
  exact H s hΛ

/-- If mathlib's `RiemannHypothesis` holds, then every *regular* zero of the
completed Riemann zeta function lies on the critical line.

Here "regular" means the archimedean factor is nonzero (`Gammaℝ s ≠ 0`) and
`s ≠ 1`.  This is the exact converse endpoint for the nontrivial zeros; without
the regularity filter, the completed-zeta statement is stronger than RH because
it also speaks about the archimedean factor's exceptional zero set. -/
theorem completedZeta_regular_zeros_on_line_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2 := by
  intro s hΛ hG hne1
  have hs0 : s ≠ 0 := by
    intro hs
    apply hG
    rw [Gammaℝ_eq_zero_iff]
    exact ⟨0, by simp [hs]⟩
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    apply hG
    rw [Gammaℝ_eq_zero_iff]
    refine ⟨n + 1, ?_⟩
    rw [hn]
    push_cast
    ring
  exact hRH s hzeta htriv hne1

/-- If every regular zero of the completed Riemann zeta function lies on the
critical line, then mathlib's `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_completedZeta_regular_zeros_on_line
    (H : ∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hs htriv hne1
  -- `s ≠ 0`, since `ζ(0) = -1/2 ≠ 0`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  -- `Gammaℝ s ≠ 0`: its zeros are `{0, -2, -4, …}`, all excluded here.
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ m =>
        exact htriv ⟨m, by push_cast at hn ⊢; linear_combination hn⟩
  -- `ζ = Λ / Gammaℝ` with `Gammaℝ s ≠ 0` and `ζ s = 0` forces `Λ s = 0`.
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right hG
  exact H s hΛ hG hne1

/-- The exact regular-zero completed-zeta endpoint is equivalent to mathlib's
official `RiemannHypothesis`.

The unfiltered theorem `riemannHypothesis_of_completedZeta_zeros_on_line` above
remains a convenient sufficient condition.  This iff is the precise statement
for nontrivial completed-zeta zeros, with the Gamma-factor exceptional set and
the pole point filtered out. -/
theorem riemannHypothesis_iff_completedZeta_regular_zeros_on_line :
    RiemannHypothesis ↔
      (∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2) := by
  constructor
  · exact completedZeta_regular_zeros_on_line_of_riemannHypothesis
  · exact riemannHypothesis_of_completedZeta_regular_zeros_on_line

/-- The Riemann `Ξ` function in the symmetric real variable: `Ξ(z) = Λ(1/2 + i z)`.

This is the object on which the Jensen / Laguerre–Pólya real-rootedness analysis
operates: `Λ(s) = Λ(1-s)` becomes evenness of `Ξ`, the critical line `Re s = 1/2`
becomes the real axis `Im z = 0`.

This is the raw completed-zeta wrapper.  The exact RH endpoint is reality of the
*regular* zeros below; reality of all raw `Ξ` zeros is a stronger sufficient
condition. -/
noncomputable def riemannXi (z : ℂ) : ℂ := completedRiemannZeta (1 / 2 + Complex.I * z)

/-- A zero of the raw `Ξ(z) = Λ(1/2 + i z)` endpoint that lies away from the
Gamma-factor exceptional set and the pole point.  This is the exact
nontrivial-zero predicate corresponding to mathlib's `RiemannHypothesis`. -/
def riemannXiRegularZero (z : ℂ) : Prop :=
  riemannXi z = 0 ∧ Gammaℝ (1 / 2 + Complex.I * z) ≠ 0 ∧ (1 / 2 + Complex.I * z) ≠ 1

/-- The change of variables `s = 1/2 + i z` sends a zero of `Λ` to a zero of `Ξ`. -/
theorem riemannXi_eq_zero_iff_completedZeta {s : ℂ} :
    riemannXi (-Complex.I * (s - 1 / 2)) = completedRiemannZeta s := by
  unfold riemannXi
  congr 1
  have hII : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I]; ring
  calc
    1 / 2 + Complex.I * (-Complex.I * (s - 1 / 2))
        = 1 / 2 + Complex.I * (-Complex.I) * (s - 1 / 2) := by ring
    _ = 1 / 2 + 1 * (s - 1 / 2) := by rw [hII]
    _ = s := by ring

/-- A zero of `Ξ` is, definitionally, a zero of `Λ` at `s = 1/2 + i z`. -/
theorem riemannXi_zero_iff_completedZeta_at_half_add (z : ℂ) :
    riemannXi z = 0 ↔ completedRiemannZeta (1 / 2 + Complex.I * z) = 0 := by
  rfl

/-- If all completed-zeta zeros lie on the critical line, then all `Ξ` zeros
are real. -/
theorem riemannXi_zeros_real_of_completedZeta_zeros_on_line
    (H : ∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2) :
    ∀ z : ℂ, riemannXi z = 0 → z.im = 0 := by
  intro z hz
  unfold riemannXi at hz
  have hline : (1 / 2 + Complex.I * z).re = 1 / 2 := H _ hz
  simp [Complex.add_re, Complex.mul_re] at hline
  linarith [hline]

/-- If all `Ξ` zeros are real, then every zero of the completed zeta function
lies on the critical line. -/
theorem completedZeta_zeros_on_line_of_riemannXi_zeros_real
    (H : ∀ z : ℂ, riemannXi z = 0 → z.im = 0) :
    ∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs
  have hXi : riemannXi (-Complex.I * (s - 1 / 2)) = 0 := by
    rw [riemannXi_eq_zero_iff_completedZeta]
    exact hs
  have him : (-Complex.I * (s - 1 / 2)).im = 0 := H _ hXi
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    Complex.sub_re, Complex.sub_im] at him
  norm_num at him
  linarith [him]

/-- The completed-zeta critical-line endpoint is equivalent to reality of all
zeros of `Ξ`.  This is only a change of variables; it is not an RH proof. -/
theorem completedZeta_zeros_on_line_iff_riemannXi_zeros_real :
    (∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2) ↔
      (∀ z : ℂ, riemannXi z = 0 → z.im = 0) := by
  constructor
  · exact riemannXi_zeros_real_of_completedZeta_zeros_on_line
  · exact completedZeta_zeros_on_line_of_riemannXi_zeros_real

/-- The regular completed-zeta endpoint transports to the regular `Ξ` endpoint. -/
theorem regular_riemannXi_zeros_real_of_completedZeta_regular_zeros_on_line
    (H : ∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2) :
    ∀ z : ℂ, riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  rcases hz with ⟨hXi, hG, hne1⟩
  unfold riemannXi at hXi
  have hline : (1 / 2 + Complex.I * z).re = 1 / 2 := H _ hXi hG hne1
  simp [Complex.add_re, Complex.mul_re] at hline
  linarith [hline]

/-- The regular `Ξ` endpoint transports back to the regular completed-zeta endpoint. -/
theorem completedZeta_regular_zeros_on_line_of_regular_riemannXi_zeros_real
    (H : ∀ z : ℂ, riemannXiRegularZero z → z.im = 0) :
    ∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2 := by
  intro s hs hG hne1
  let z : ℂ := -Complex.I * (s - 1 / 2)
  have hscoord : 1 / 2 + Complex.I * z = s := by
    dsimp [z]
    have hII : Complex.I * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    calc
      1 / 2 + Complex.I * (-Complex.I * (s - 1 / 2))
          = 1 / 2 + Complex.I * (-Complex.I) * (s - 1 / 2) := by ring
      _ = 1 / 2 + 1 * (s - 1 / 2) := by rw [hII]
      _ = s := by ring
  have hreg : riemannXiRegularZero z := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [z]
      rw [riemannXi_eq_zero_iff_completedZeta]
      exact hs
    · change Gammaℝ (1 / 2 + Complex.I * z) ≠ 0
      rw [hscoord]
      exact hG
    · change (1 / 2 + Complex.I * z) ≠ 1
      rw [hscoord]
      exact hne1
  have him : z.im = 0 := H z hreg
  dsimp [z] at him
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    Complex.sub_re, Complex.sub_im] at him
  norm_num at him
  linarith [him]

/-- The regular completed-zeta endpoint is equivalent to reality of all regular
`Ξ` zeros.  This is the precise change of variables for the nontrivial-zero
endpoint. -/
theorem completedZeta_regular_zeros_on_line_iff_regular_riemannXi_zeros_real :
    (∀ s : ℂ, completedRiemannZeta s = 0 → Gammaℝ s ≠ 0 → s ≠ 1 → s.re = 1 / 2) ↔
      (∀ z : ℂ, riemannXiRegularZero z → z.im = 0) := by
  constructor
  · exact regular_riemannXi_zeros_real_of_completedZeta_regular_zeros_on_line
  · exact completedZeta_regular_zeros_on_line_of_regular_riemannXi_zeros_real

/-- Mathlib's `RiemannHypothesis` is exactly reality of all regular `Ξ` zeros. -/
theorem riemannHypothesis_iff_regular_riemannXi_zeros_real :
    RiemannHypothesis ↔ (∀ z : ℂ, riemannXiRegularZero z → z.im = 0) := by
  exact riemannHypothesis_iff_completedZeta_regular_zeros_on_line.trans
    completedZeta_regular_zeros_on_line_iff_regular_riemannXi_zeros_real

/-- **The functional equation as a reflection: `Ξ` is even.**
`Λ(1-s) = Λ(s)` (`completedRiemannZeta_one_sub`) becomes, in the `Ξ` variable
`s = 1/2 + i z`, the evenness `Ξ(-z) = Ξ(z)`.  This is the formal heart of the
"functional equation = reflection about the critical line" structure: the
parity `z ↦ -z` (PT/Bisognano–Wichmann reflection) is a symmetry of `Ξ`, whose
fixed-point set `Im z = 0` is the critical line.  Kernel-checked, unconditional. -/
theorem riemannXi_even (z : ℂ) : riemannXi (-z) = riemannXi z := by
  unfold riemannXi
  rw [show (1 / 2 + Complex.I * (-z)) = 1 - (1 / 2 + Complex.I * z) by ring]
  exact completedRiemannZeta_one_sub (1 / 2 + Complex.I * z)

/-- The regular `Ξ` zero predicate is invariant under the functional-equation
reflection `z ↦ -z`.

The zero equation follows from evenness of `Ξ`.  The regularity filters need one
extra classical input: if the reflected point hit a Gamma-factor exceptional
zero, then the original point would lie in `Re s ≥ 1`; since `Λ(s)=0` and
`Gammaℝ s ≠ 0`, this would force `ζ(s)=0`, contradicting the nonvanishing of
the Riemann zeta function on that half-plane. -/
theorem riemannXiRegularZero_neg (z : ℂ)
    (hz : riemannXiRegularZero z) : riemannXiRegularZero (-z) := by
  let s : ℂ := 1 / 2 + Complex.I * z
  have hs_neg : 1 / 2 + Complex.I * (-z) = 1 - s := by
    dsimp [s]
    ring
  rcases hz with ⟨hXi, hG, _hne1⟩
  have hΛ : completedRiemannZeta s = 0 := by
    simpa [s, riemannXi] using hXi
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannXi_even]
    exact hXi
  · rw [hs_neg]
    intro hG1
    rw [Gammaℝ_eq_zero_iff] at hG1
    rcases hG1 with ⟨n, hn⟩
    have hs_eq : s = 1 + (2 * n : ℂ) := by
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - (-(2 * n : ℂ)) := by rw [hn]
        _ = 1 + (2 * n : ℂ) := by ring
    have h_re : 1 ≤ s.re := by
      rw [hs_eq]
      simp
    have hs0 : s ≠ 0 := by
      intro h0
      have hre0 : s.re = 0 := by
        rw [h0]
        simp
      linarith
    have hzeta_zero : riemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
    exact (riemannZeta_ne_zero_of_one_le_re h_re) hzeta_zero
  · rw [hs_neg]
    intro h1
    have hs0 : s = 0 := by
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - 1 := by rw [h1]
        _ = 0 := by ring
    apply hG
    rw [Gammaℝ_eq_zero_iff]
    exact ⟨0, by simp [s] at hs0; simp [hs0]⟩

/-- The regular `Ξ` zero set is symmetric under `z ↦ -z`. -/
theorem riemannXiRegularZero_neg_iff (z : ℂ) :
    riemannXiRegularZero (-z) ↔ riemannXiRegularZero z := by
  constructor
  · intro h
    simpa using riemannXiRegularZero_neg (-z) h
  · exact riemannXiRegularZero_neg z

/-- **Brick 2 (Ξ ⇒ RH endpoint).**
If every zero of the raw Riemann `Ξ` wrapper is real (`Im z = 0`), then the
Riemann Hypothesis holds.  This is a stronger sufficient condition; the exact
RH-equivalent endpoint is `riemannHypothesis_iff_regular_riemannXi_zeros_real`. -/
theorem riemannHypothesis_of_riemannXi_zeros_real
    (H : ∀ z : ℂ, riemannXi z = 0 → z.im = 0) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_completedZeta_zeros_on_line
    (completedZeta_zeros_on_line_of_riemannXi_zeros_real H)

/-!
## The reduction map and the one open input

Bricks 1–2 above are unconditional and kernel-checked: they carry mathlib's
official `RiemannHypothesis` back to the statement *"every regular zero of
`Ξ` is real"*.

The remaining distance is two named inputs, of **very different status**:

* **`hClassicalGate`** — the Pólya–Jensen + Hadamard criterion: hyperbolicity of
  all `Ξ` Jensen sections implies reality of all regular `Ξ` zeros.  This is **known
  classical mathematics** (Pólya 1927; Csordás–Norfolk–Varga 1986; Hadamard
  factorization of order-1 entire functions).  It is not in mathlib and not
  formalized here, but it is a *general criterion* — it is **not** RH, and it is
  not the open problem.

* **`hHyperbolic`** — *"every `Ξ` Jensen section is hyperbolic (all roots real)"*.
  This is what **Theorem M** (proven, Lean 4, for the model family `Ψ_d`) **plus
  the still-open transport / Euler-trace-barrier bridge** must supply.  It is
  RH-equivalent; it is the genuinely **open** content of RH, and it is **not**
  proven anywhere (the workspace's 400+ research rounds reduce RH to exactly this
  bridge, which the fake-family / criticality wall has so far blocked).

The lemma below is therefore a *conditional* and emphatically **not a proof of
RH**: it only certifies that the reduction logic is correct — RH follows from the
classical gate applied to the open hyperbolicity input.  Theorem M is proven, but
Theorem M does not prove RH by itself. -/
theorem riemannHypothesis_of_classicalGate_and_hyperbolicity
    {XiHyperbolic : Prop}
    (hClassicalGate : XiHyperbolic → (∀ z : ℂ, riemannXiRegularZero z → z.im = 0))
    (hHyperbolic : XiHyperbolic) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_regular_riemannXi_zeros_real).2 (hClassicalGate hHyperbolic)

end RHReduction
end JensenLadder
