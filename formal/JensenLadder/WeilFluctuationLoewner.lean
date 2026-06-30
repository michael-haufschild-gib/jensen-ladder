import Mathlib

/-!
# The sin-Loewner factorization: the formal kernel of the Weil-fluctuation boundedness (V1)

The CCM Weil-form fluctuation `M_int = W_R + P` decomposes as
`M_int = (1/π) ∫ L_s(x) dW(x)` (the explicit-formula distribution `W` averaged against the
sin-Loewner family `L_s(x)[n,m] = (sin(2πnx/L) − sin(2πmx/L))/(n−m)`); see
`docs/rh/dyson_resolvent_lowerbound_target_20260618.md` §6–8. The uniform boundedness of
`M_int` in the grid size `N` (V1: `μ_∞` has bounded support, hence is determinate, V3) rests on
the fact that each Loewner kernel of `sin` is a **bounded unitary-modulated Toeplitz** operator,
which in turn rests on the exact entry-level factorization proved here:

`(sin a − sin b)/(a − b) = cos((a+b)/2) · ( sin((a−b)/2) / ((a−b)/2) )`  (a `cos`-modulation
times a `sinc` of the *difference* — i.e. modulation × Toeplitz),

and on the elementary `1`-Lipschitz bound `|(sin a − sin b)/(a − b)| ≤ 1`.

This module formalizes those two facts (RH-free; pure real analysis). It is the formal kernel of
the V1 mechanism; the full operator-norm bound (Toeplitz symbol sup-norm) is the remaining
analytic step. It does NOT prove RH; the RH residue is the *spectral inertia* of `∫ L_s dW`.
Axiom-clean.
-/

namespace JensenLadder
namespace WeilFluctuationLoewner

/-- **Sin-Loewner factorization.** The divided difference of `sin` factors as a `cos`-modulation
of the midpoint times the `sinc` of the half-difference — the `modulation × Toeplitz` structure
behind the uniform boundedness of the Weil-fluctuation Loewner operators. -/
theorem sin_dividedDifference (a b : ℝ) (h : a ≠ b) :
    (Real.sin a - Real.sin b) / (a - b)
      = Real.cos ((a + b) / 2) * (Real.sin ((a - b) / 2) / ((a - b) / 2)) := by
  have hab : a - b ≠ 0 := sub_ne_zero.mpr h
  have h2 : (a - b) / 2 ≠ 0 := div_ne_zero hab (by norm_num)
  rw [Real.sin_sub_sin]
  field_simp

/-- **Uniform entry bound.** `sin` is `1`-Lipschitz, so every entry of a sin-Loewner matrix is
bounded by `1`, uniformly: `|(sin a − sin b)/(a − b)| ≤ 1`. -/
theorem abs_sin_dividedDifference_le_one (a b : ℝ) (h : a ≠ b) :
    |(Real.sin a - Real.sin b) / (a - b)| ≤ 1 := by
  have hab : a - b ≠ 0 := sub_ne_zero.mpr h
  rw [abs_div]
  rw [div_le_one (by positivity)]
  calc |Real.sin a - Real.sin b| ≤ |a - b| := Real.abs_sin_sub_sin_le a b
    _ = |a - b| * 1 := (mul_one _).symm
    _ ≤ |a - b| := le_of_eq (mul_one _)

/-- **Sin-Loewner SOS-difference (entry level).** Applying the cosine addition formula to the
midpoint modulation of `sin_dividedDifference` splits the Loewner kernel of `sin` into a
*difference of two products*, each a diagonal-congruence of the same `sinc` divided-difference:

`(sin a − sin b)/(a − b)`
  `= cos(a/2)·cos(b/2) · s  −  sin(a/2)·sin(b/2) · s`,  where `s = sin((a−b)/2)/((a−b)/2)`.

At the matrix level (`a = θ_n`, `b = θ_m`, `s[n,m] = sinc((θ_n−θ_m)/2)` the Bochner-PSD sinc
Toeplitz kernel `T`, `E = diag(cos(θ_n/2))`, `F = diag(sin(θ_n/2))`) this is exactly the
sum-of-squares-difference factorization `L_s = E T E − F T F`: a difference of two diagonally
congruent copies of one PSD Toeplitz kernel. Since diagonal congruence preserves positive
semidefiniteness, `E T E ⪰ 0` and `F T F ⪰ 0`, so the Weil-fluctuation Loewner operator is a
genuine `(PSD) − (PSD)` difference — the structural origin of its inertia being the RH residue
(see `docs/rh/dyson_resolvent_lowerbound_target_20260618.md` §8, SOS-difference / chirp form).
RH-free; pure real analysis. Axiom-clean. -/
theorem sin_dividedDifference_sos (a b : ℝ) (h : a ≠ b) :
    (Real.sin a - Real.sin b) / (a - b)
      = Real.cos (a / 2) * Real.cos (b / 2) * (Real.sin ((a - b) / 2) / ((a - b) / 2))
        - Real.sin (a / 2) * Real.sin (b / 2) * (Real.sin ((a - b) / 2) / ((a - b) / 2)) := by
  rw [sin_dividedDifference a b h]
  have hmid : (a + b) / 2 = a / 2 + b / 2 := by ring
  rw [hmid, Real.cos_add]
  ring

open Matrix in
/-- **Diagonal congruence preserves PSD.** For any real diagonal `D = diagonal d` and any
positive-semidefinite `T`, the congruence `D · T · D` is again positive semidefinite.

This is the matrix-level upgrade of `sin_dividedDifference_sos`: with `T` the (Bochner-PSD) sinc
Toeplitz kernel, `E = diagonal (cos(θ·/2))` and `F = diagonal (sin(θ·/2))`, it yields
`E T E ⪰ 0` **and** `F T F ⪰ 0`. Hence the Weil-fluctuation Loewner operator
`L_s = E T E − F T F` is a genuine difference of two positive-semidefinite matrices — both halves
unconditionally `⪰ 0`, so the entire RH content is concentrated in the *inertia of the signed
difference*. (A real diagonal matrix is self-adjoint, `Dᴴ = D`, so this is the `B = D` case of
`Matrix.PosSemidef.mul_mul_conjTranspose_same`.) RH-free. Axiom-clean. -/
theorem diagonal_conj_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.PosSemidef) (d : n → ℝ) :
    (Matrix.diagonal d * T * Matrix.diagonal d).PosSemidef := by
  have hD : (Matrix.diagonal d)ᴴ = Matrix.diagonal d := by
    rw [Matrix.diagonal_conjTranspose]; simp
  have h := hT.mul_mul_conjTranspose_same (Matrix.diagonal d)
  rwa [hD] at h

/-- **Matrix-level SOS-difference (general Toeplitz kernel).** For any difference-kernel
`g : ℝ → ℝ` and grid `θ : ι → ℝ`, the cosine-of-midpoint-modulated Toeplitz matrix factors as
`E T E − F T F`:

`(cos((θᵢ+θⱼ)/2) · g(θᵢ−θⱼ))ᵢⱼ = E·T·E − F·T·F`,

where `T = (g(θᵢ−θⱼ))ᵢⱼ` is the Toeplitz matrix of `g`, `E = diagonal(cos(θ·/2))`,
`F = diagonal(sin(θ·/2))`. This is the matrix-level statement of `sin_dividedDifference_sos`
(entry-level), now general in the kernel — the structure is purely the cosine-addition factoring
of the midpoint modulation, independent of `g`. Specializing `g = sinc` and using
`sin_dividedDifference` recovers the Weil-fluctuation sin-Loewner operator. RH-free; pure algebra.
Axiom-clean. -/
theorem modulated_toeplitz_sos_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ℝ → ℝ) (θ : ι → ℝ) :
    Matrix.of (fun i j => Real.cos ((θ i + θ j) / 2) * g (θ i - θ j))
      = Matrix.diagonal (fun i => Real.cos (θ i / 2))
          * Matrix.of (fun i j => g (θ i - θ j))
          * Matrix.diagonal (fun i => Real.cos (θ i / 2))
        - Matrix.diagonal (fun i => Real.sin (θ i / 2))
          * Matrix.of (fun i j => g (θ i - θ j))
          * Matrix.diagonal (fun i => Real.sin (θ i / 2)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  have hmid : (θ i + θ j) / 2 = θ i / 2 + θ j / 2 := by ring
  rw [hmid, Real.cos_add]; ring

/-- **The modulated Toeplitz operator is a difference of two PSD matrices.** If the underlying
Toeplitz kernel `T = (g(θᵢ−θⱼ))ᵢⱼ` is positive semidefinite (for the Weil fluctuation, `g = sinc`
is PSD by Bochner), then the cosine-modulated Loewner operator splits as `A − B` with both
`A = E T E ⪰ 0` and `B = F T F ⪰ 0` (by `diagonal_conj_posSemidef`). This is the matrix-level V1
payload: the Weil-fluctuation Loewner operator is unconditionally a `(PSD) − (PSD)` difference, so
its RH content is entirely the *inertia of the signed difference* — not any positivity that the
two halves individually lack. RH-free. Axiom-clean. -/
theorem modulated_toeplitz_psd_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ℝ → ℝ) (θ : ι → ℝ)
    (hT : (Matrix.of (fun i j => g (θ i - θ j))).PosSemidef) :
    ∃ A B : Matrix ι ι ℝ, A.PosSemidef ∧ B.PosSemidef ∧
      Matrix.of (fun i j => Real.cos ((θ i + θ j) / 2) * g (θ i - θ j)) = A - B :=
  ⟨_, _, diagonal_conj_posSemidef hT (fun i => Real.cos (θ i / 2)),
        diagonal_conj_posSemidef hT (fun i => Real.sin (θ i / 2)),
        modulated_toeplitz_sos_difference g θ⟩

/-- **Sin-Loewner = cosine-modulated sinc (off-diagonal).** The divided difference of `sin` is
exactly the `cos`-of-midpoint modulation of the *Mathlib* `Real.sinc` of the half-difference:
`(sin a − sin b)/(a − b) = cos((a+b)/2) · sinc((a−b)/2)` for `a ≠ b`. This identifies the
difference-kernel of the general `modulated_toeplitz_sos_difference` (take `g = fun t ↦ sinc(t/2)`,
so `g(θᵢ−θⱼ) = sinc((θᵢ−θⱼ)/2)`) with the genuine sin-Loewner operator of the Weil fluctuation.
RH-free. Axiom-clean. -/
theorem sinLoewner_eq_modulated_sinc (a b : ℝ) (h : a ≠ b) :
    (Real.sin a - Real.sin b) / (a - b)
      = Real.cos ((a + b) / 2) * Real.sinc ((a - b) / 2) := by
  have h2 : (a - b) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h) (by norm_num)
  rw [Real.sinc_of_ne_zero h2]
  exact sin_dividedDifference a b h

/-- **Sin-Loewner = cosine-modulated sinc (on-diagonal).** At `a = b` the modulated sinc kernel
takes the value `cos a` — the continuous (derivative-of-`sin`) extension that the divided
difference `0/0` would otherwise miss: `cos((a+a)/2) · sinc((a−a)/2) = cos a` (since `sinc 0 = 1`).
Together with `sinLoewner_eq_modulated_sinc` this shows the modulated `Real.sinc` Toeplitz kernel
reproduces the full sin-Loewner matrix — divided difference off-diagonal, derivative on-diagonal —
with no special-casing needed in the matrix definition. RH-free. Axiom-clean. -/
theorem modulated_sinc_diag (a : ℝ) :
    Real.cos ((a + a) / 2) * Real.sinc ((a - a) / 2) = Real.cos a := by
  have h0 : (a - a) / 2 = 0 := by ring
  rw [h0, Real.sinc_zero, mul_one]
  congr 1; ring

/-- **Bochner integral representation of `sinc`.** `Real.sinc x = ∫₀¹ cos(x·t) dt`. This is the
finite-dimensional gateway to positive-definiteness of the sinc Toeplitz kernel: `cos(x·t)` is a
character, so averaging it over `t ∈ [0,1]` exhibits `sinc` as a (non-normalized) Fourier transform
of a nonnegative measure (the box on `[0,1]`). Combined with the cosine subtraction formula
`cos((θᵢ−θⱼ)t) = cos(θᵢt)cos(θⱼt) + sin(θᵢt)sin(θⱼt)`, this is the route to
`(sinc(θᵢ−θⱼ))ᵢⱼ ⪰ 0` (every quadratic form `= ∫₀¹[(∑vᵢcos θᵢt)² + (∑vᵢsin θᵢt)²]dt ≥ 0`), the one
RH-free input still missing from the `modulated_toeplitz_psd_difference` chain. RH-free. Axiom-clean. -/
theorem sinc_eq_integral (x : ℝ) :
    Real.sinc x = ∫ t in (0:ℝ)..1, Real.cos (x * t) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    rw [Real.sinc_zero]
    simp
  · rw [Real.sinc_of_ne_zero hx,
        intervalIntegral.integral_comp_mul_left Real.cos hx,
        mul_zero, mul_one, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul]
    ring

open Matrix in
/-- **The sinc Toeplitz kernel is positive semidefinite (Bochner).** For any grid `θ : ι → ℝ`, the
matrix `T = (sinc(θᵢ − θⱼ))ᵢⱼ` is `PosSemidef`. Proof: `sinc` is even (so `T` is Hermitian), and for
any `v` the quadratic form is a nonnegative integral of a sum of squares,
`∑ᵢⱼ vᵢvⱼ sinc(θᵢ−θⱼ) = ∫₀¹ [(∑ᵢ vᵢ cos(θᵢt))² + (∑ᵢ vᵢ sin(θᵢt))²] dt ≥ 0`,
using `sinc_eq_integral`, the cosine subtraction formula, the sum↔integral interchange (each summand
continuous ⟹ interval-integrable), and `intervalIntegral.integral_nonneg`.

This **discharges the standing RH-free hypothesis** of `modulated_toeplitz_psd_difference`: with the
sinc Toeplitz kernel now proven PSD, the Weil-fluctuation sin-Loewner operator
`L_s = E T E − F T F` is *unconditionally* a difference of two positive-semidefinite matrices (see
`sinLoewner_psd_difference`). The only content beyond this point is the inertia of the signed
difference — the RH residue. RH-free; pure analysis. Axiom-clean. -/
theorem sincToeplitz_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    (Matrix.of (fun i j => Real.sinc (θ i - θ j))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [show θ j - θ i = -(θ i - θ j) by ring, Real.sinc_neg]
  · intro v
    have hsv : (star v : ι → ℝ) = v := by funext i; simp
    have e1 : star v ⬝ᵥ (Matrix.of (fun i j => Real.sinc (θ i - θ j)) *ᵥ v)
        = ∑ i, ∑ j, v i * v j * Real.sinc (θ i - θ j) := by
      rw [hsv]
      simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have hcont : ∀ i j : ι, Continuous (fun t => v i * v j * Real.cos ((θ i - θ j) * t)) := by
      intro i j; fun_prop
    have hcontsum : ∀ i : ι, Continuous (fun t => ∑ j, v i * v j * Real.cos ((θ i - θ j) * t)) := by
      intro i; fun_prop
    have epair : ∀ i j : ι, v i * v j * Real.sinc (θ i - θ j)
        = ∫ t in (0:ℝ)..1, v i * v j * Real.cos ((θ i - θ j) * t) := by
      intro i j; rw [sinc_eq_integral, ← intervalIntegral.integral_const_mul]
    have e2 : ∑ i, ∑ j, v i * v j * Real.sinc (θ i - θ j)
        = ∫ t in (0:ℝ)..1, ∑ i, ∑ j, v i * v j * Real.cos ((θ i - θ j) * t) := by
      simp_rw [epair]
      rw [intervalIntegral.integral_finsetSum (fun i _ => (hcontsum i).intervalIntegrable 0 1)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable 0 1)]
    have e3 : ∀ t : ℝ, ∑ i, ∑ j, v i * v j * Real.cos ((θ i - θ j) * t)
        = (∑ i, v i * Real.cos (θ i * t)) ^ 2 + (∑ i, v i * Real.sin (θ i * t)) ^ 2 := by
      intro t
      have hcs : ∀ i j : ι, Real.cos ((θ i - θ j) * t)
          = Real.cos (θ i * t) * Real.cos (θ j * t) + Real.sin (θ i * t) * Real.sin (θ j * t) := by
        intro i j; rw [show (θ i - θ j) * t = θ i * t - θ j * t by ring, Real.cos_sub]
      simp_rw [hcs, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      · rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    rw [e1, e2]
    simp_rw [e3]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u _
    positivity

/-- **The Weil-fluctuation sin-Loewner operator is unconditionally a difference of two PSD
matrices.** No hypothesis: the modulated-sinc form of the sin-Loewner kernel,
`(cos((θᵢ+θⱼ)/2) · sinc((θᵢ−θⱼ)/2))ᵢⱼ`, equals `A − B` with `A, B ⪰ 0`. This is the V1 mechanism
fully discharged on the RH-free side: combining `modulated_toeplitz_psd_difference` (the `E T E − F T F`
split) with `sincToeplitz_posSemidef` (the kernel `T = sinc` is PSD, applied to the half-grid `θ/2`).
By `sinLoewner_eq_modulated_sinc`/`modulated_sinc_diag` the modulated-sinc matrix IS the genuine
sin-Loewner matrix (divided difference off-diagonal, derivative on-diagonal). Hence the entire
RH content of the Weil fluctuation is the **inertia of the signed difference `A − B`** — the single
remaining (RH-equivalent) question. RH-free. Axiom-clean. -/
theorem sinLoewner_psd_difference {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    ∃ A B : Matrix ι ι ℝ, A.PosSemidef ∧ B.PosSemidef ∧
      Matrix.of (fun i j => Real.cos ((θ i + θ j) / 2) * Real.sinc ((θ i - θ j) / 2)) = A - B := by
  have hT : (Matrix.of (fun i j => Real.sinc (θ i / 2 - θ j / 2)) : Matrix ι ι ℝ).PosSemidef :=
    sincToeplitz_posSemidef (fun i => θ i / 2)
  have heq : (Matrix.of (fun i j => Real.sinc (θ i / 2 - θ j / 2)) : Matrix ι ι ℝ)
           = Matrix.of (fun i j => Real.sinc ((θ i - θ j) / 2)) := by
    ext i j; simp only [Matrix.of_apply]; congr 1; ring
  rw [heq] at hT
  exact modulated_toeplitz_psd_difference (fun t => Real.sinc (t / 2)) θ hT

open Matrix in
/-- **Inertia mechanism (kernel).** If `A − B` is a difference with `B` positive semidefinite, then
the quadratic form `x ↦ x ⬝ᵥ (A − B) *ᵥ x` is `≤ 0` on the kernel of the positive part `A` (any `x`
with `A *ᵥ x = 0`): there `x ⬝ᵥ (A − B) *ᵥ x = −(x ⬝ᵥ B *ᵥ x) ≤ 0`.

This is the precise RH-free reason the Weil-fluctuation operator `L_s = A − B` (with `A = E T E`,
`B = F T F`, both PSD by `sinLoewner_psd_difference`) has its *positive directions confined to the
range of `A`* — i.e. its positive inertia is bounded by `rank A`. That bounded positive inertia is
exactly the Lorentzian / "one positive direction" signature the Stage-2 carrier needs (cf. the
hawking Stage-2 test: ζ's intersection candidate has inertia `(1, n−1)`). RH-free. Axiom-clean. -/
theorem psdDiff_nonpos_on_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hB : B.PosSemidef) {x : ι → ℝ} (hx : A *ᵥ x = 0) :
    x ⬝ᵥ ((A - B) *ᵥ x) ≤ 0 := by
  rw [sub_mulVec, dotProduct_sub, hx, dotProduct_zero, zero_sub]
  have hsx : (star x : ι → ℝ) = x := by funext i; simp
  have h := hB.dotProduct_mulVec_nonneg x
  rw [hsx] at h; linarith

open Matrix in
/-- **Inertia mechanism (monotonicity).** Subtracting a positive-semidefinite `B` only *decreases*
the quadratic form: `x ⬝ᵥ (A − B) *ᵥ x ≤ x ⬝ᵥ A *ᵥ x` for all `x`. Together with
`psdDiff_nonpos_on_kernel`, this pins the inertia of the Weil fluctuation: the form is everywhere
dominated by its PSD positive part `A` and is non-positive wherever `A` vanishes, so all positive
inertia originates in `A`. RH-free. Axiom-clean. -/
theorem psdDiff_le_pos_part {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hB : B.PosSemidef) (x : ι → ℝ) :
    x ⬝ᵥ ((A - B) *ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub]
  have hsx : (star x : ι → ℝ) = x := by funext i; simp
  have h := hB.dotProduct_mulVec_nonneg x
  rw [hsx] at h; linarith

open Matrix in
/-- **Injectivity seed for the inertia bound.** If the form `A − B` (with `B` positive semidefinite)
is *strictly positive* at `x`, then `A *ᵥ x ≠ 0`: a positive direction of `A − B` cannot lie in the
kernel of the positive part `A`. (Immediate contrapositive of `psdDiff_nonpos_on_kernel`.) This is
the linear-algebra seed of the exact positive-inertia bound `n₊(A − B) ≤ rank A`: every
positive-definite direction injects into the range of `A`. RH-free. Axiom-clean. -/
theorem psdDiff_pos_imp_pos_part_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hB : B.PosSemidef) {x : ι → ℝ}
    (hpos : 0 < x ⬝ᵥ ((A - B) *ᵥ x)) : A *ᵥ x ≠ 0 := by
  intro hx
  exact absurd hpos (not_lt.mpr (psdDiff_nonpos_on_kernel hB hx))

open Matrix in
/-- **The cosine Toeplitz kernel is positive semidefinite.** For any grid `θ : ι → ℝ`, the matrix
`(cos(θᵢ − θⱼ))ᵢⱼ` is `PosSemidef` — it is the rank-≤2 Gram matrix of the unit vectors
`(cos θᵢ, sin θᵢ)`: `cos(θᵢ−θⱼ) = cos θᵢ cos θⱼ + sin θᵢ sin θⱼ`, so the quadratic form is
`(∑ᵢ vᵢ cos θᵢ)² + (∑ᵢ vᵢ sin θᵢ)² ≥ 0`. This is the foundational Bochner positivity behind
`sincToeplitz_posSemidef` (since `sinc x = ∫₀¹ cos(x·t) dt`, the sinc Toeplitz kernel is the average
over `t` of the cosine Toeplitz kernels of the scaled grids `θ·t`). RH-free. Axiom-clean. -/
theorem cosToeplitz_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    (Matrix.of (fun i j => Real.cos (θ i - θ j))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [show θ j - θ i = -(θ i - θ j) by ring, Real.cos_neg]
  · intro v
    have hsv : (star v : ι → ℝ) = v := by funext i; simp
    have e1 : star v ⬝ᵥ (Matrix.of (fun i j => Real.cos (θ i - θ j)) *ᵥ v)
        = ∑ i, ∑ j, v i * v j * Real.cos (θ i - θ j) := by
      rw [hsv]; simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    rw [e1]
    have e2 : ∑ i, ∑ j, v i * v j * Real.cos (θ i - θ j)
        = (∑ i, v i * Real.cos (θ i)) ^ 2 + (∑ i, v i * Real.sin (θ i)) ^ 2 := by
      have hcs : ∀ i j : ι, Real.cos (θ i - θ j)
          = Real.cos (θ i) * Real.cos (θ j) + Real.sin (θ i) * Real.sin (θ j) :=
        fun i j => Real.cos_sub (θ i) (θ j)
      simp_rw [hcs, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      · rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    rw [e2]; positivity

open Matrix in
/-- **PSD zero-characterization** (not in Mathlib as of v4.30.0). For a positive-semidefinite `A`,
the quadratic form vanishes at `x` iff `A` annihilates `x`: `x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0`.

Proof of the forward (hard) direction is the classical discriminant / Cauchy–Schwarz argument with
no `sqrt`: from `q(z) := z ⬝ᵥ A *ᵥ z ≥ 0` everywhere and `q(x) = 0`, expanding
`q(y + t·x) = q(y) + 2t·(y ⬝ᵥ A *ᵥ x) ≥ 0` for all real `t` (using bilinear symmetry of the
symmetric `A`) forces the linear coefficient `y ⬝ᵥ A *ᵥ x = 0` for every `y`; taking `y = A *ᵥ x`
gives `(A *ᵥ x) ⬝ᵥ (A *ᵥ x) = 0`, hence `A *ᵥ x = 0`. (Same shifted-quadratic technique as
`HodgeIndexLorentzian.hodge_index_iff`.)

This is the missing pillar of the exact positive-inertia bound `n₊(A − B) ≤ rank A`: combined with
`psdDiff_le_pos_part`, it shows any direction on which `A − B` is strictly positive has `A *ᵥ x ≠ 0`,
so the map `x ↦ A *ᵥ x` is injective on every positive-definite subspace. RH-free. Axiom-clean. -/
theorem posSemidef_dotProduct_self_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · intro hx
    have hAT : Aᵀ = A := by
      ext i j
      have h : Aᴴ i j = A i j := congrFun (congrFun hA.1 i) j
      rw [Matrix.conjTranspose_apply, star_trivial] at h
      rw [Matrix.transpose_apply]; exact h
    have hsymm : ∀ u w : ι → ℝ, u ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ u) := by
      intro u w
      rw [dotProduct_mulVec, ← mulVec_transpose, hAT, dotProduct_comm]
    have qnn : ∀ z : ι → ℝ, 0 ≤ z ⬝ᵥ (A *ᵥ z) := by
      intro z
      have h := hA.dotProduct_mulVec_nonneg z
      have hsz : (star z : ι → ℝ) = z := by funext i; simp
      rwa [hsz] at h
    have key : ∀ y : ι → ℝ, y ⬝ᵥ (A *ᵥ x) = 0 := by
      intro y
      have expand : ∀ t : ℝ, (y + t • x) ⬝ᵥ (A *ᵥ (y + t • x))
          = y ⬝ᵥ (A *ᵥ y) + 2 * t * (y ⬝ᵥ (A *ᵥ x)) := by
        intro t
        simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [hx, hsymm x y]; ring
      have Hpoly : ∀ t : ℝ, 0 ≤ y ⬝ᵥ (A *ᵥ y) + 2 * t * (y ⬝ᵥ (A *ᵥ x)) := by
        intro t; rw [← expand t]; exact qnn _
      by_contra hd
      have heval := Hpoly (-(y ⬝ᵥ (A *ᵥ y) + 1) / (2 * (y ⬝ᵥ (A *ᵥ x))))
      have hsimp : y ⬝ᵥ (A *ᵥ y)
          + 2 * (-(y ⬝ᵥ (A *ᵥ y) + 1) / (2 * (y ⬝ᵥ (A *ᵥ x)))) * (y ⬝ᵥ (A *ᵥ x)) = -1 := by
        field_simp
        ring
      rw [hsimp] at heval
      linarith
    exact dotProduct_self_eq_zero.mp (key (A *ᵥ x))
  · intro hx; rw [hx, dotProduct_zero]

open Matrix in
/-- **The positive-inertia bound `n₊(A − B) ≤ rank A`** (subspace form). For positive-semidefinite
`A` and `B`, any subspace `W` on which the difference form `A − B` is *positive definite*
(`∀ x ∈ W, x ≠ 0 → 0 < x ⬝ᵥ (A − B) *ᵥ x`) has dimension at most the rank of the positive part `A`:
`finrank W ≤ finrank (range A.mulVecLin)`.

This is the headline of the inertia thread and the RH-free explanation of the Stage-2 "(1, n−1)"
signature: the positive directions of the Weil fluctuation `L_s = A − B` are confined to (and inject
into) the range of its PSD positive part `A`. Proof: on `W`, `0 < x ⬝ᵥ (A−B) *ᵥ x ≤ x ⬝ᵥ A *ᵥ x`
(`psdDiff_le_pos_part`), so `x ⬝ᵥ A *ᵥ x > 0`, hence `A *ᵥ x ≠ 0`
(`posSemidef_dotProduct_self_eq_zero_iff`); thus `A.mulVecLin ∘ W.subtype` is injective, and
`finrank W = finrank (range _) ≤ finrank (range A.mulVecLin)`. Since `A = E T E` has the rank of the
sinc-Toeplitz congruence (small relative to `n` when the archimedean mode dominates), this bounds the
positive inertia. The exact *count* and the *sign* of `λ_min` (the no-margin = RH) remain open.
RH-free. Axiom-clean. -/
theorem psdDiff_finrank_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {W : Submodule ℝ (ι → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < x ⬝ᵥ ((A - B) *ᵥ x)) :
    Module.finrank ℝ W ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin) := by
  set f := A.mulVecLin.comp W.subtype with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hfx
    have hAx : A *ᵥ x = 0 := by
      have hfe : f ⟨x, hx⟩ = A *ᵥ x := by simp [hf]
      rw [hfe] at hfx; exact hfx
    rw [Submodule.mk_eq_zero]
    by_contra hxne
    have hpos := hW x hx hxne
    have hle := psdDiff_le_pos_part (A := A) hB x
    have hAxpos : (0:ℝ) < x ⬝ᵥ (A *ᵥ x) := lt_of_lt_of_le hpos hle
    rw [(posSemidef_dotProduct_self_eq_zero_iff hA x).mpr hAx] at hAxpos
    exact lt_irrefl 0 hAxpos
  calc Module.finrank ℝ W
      = Module.finrank ℝ (LinearMap.range f) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range W.subtype A.mulVecLin)

open Matrix in
/-- **Lorentzian "(1, n−1)" signature from a rank-1 positive part.** If the positive part `A` has
its range contained in a single line `ℝ ∙ u` (a *rank-≤1* PSD, e.g. the CCM archimedean main term
`W0_2 = ρ · u uᵀ` of `T3T5SumRule`), then *every* subspace on which `A − B` is positive definite has
dimension `≤ 1`: the difference has **at most one positive direction**.

This is the precise RH-free realization of the Stage-2 carrier's `(1, n−1)` signature
(hawking's Stage-2 test: ζ's `−Q_W` has exactly one positive, ample-on-boundary eigenvalue). It
specializes `psdDiff_finrank_le` to `rank A ≤ 1` via `finrank (ℝ ∙ u) ≤ 1`. The Weil fluctuation
being Lorentzian-or-negative is thus a *structural consequence* of the rank-1 archimedean term; what
it does NOT decide is whether that one positive direction actually survives (sign of `λ_min` =
no-margin = RH). RH-free. Axiom-clean. -/
theorem psdDiff_finrank_le_one_of_rangeLine {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) {u : ι → ℝ}
    (hr : LinearMap.range A.mulVecLin ≤ ℝ ∙ u)
    {W : Submodule ℝ (ι → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < x ⬝ᵥ ((A - B) *ᵥ x)) :
    Module.finrank ℝ W ≤ 1 := by
  have h1 := psdDiff_finrank_le hA hB hW
  have h2 : Module.finrank ℝ (LinearMap.range A.mulVecLin) ≤ Module.finrank ℝ (ℝ ∙ u) :=
    Submodule.finrank_mono hr
  have h3 : Module.finrank ℝ (ℝ ∙ u) ≤ 1 := by
    rcases eq_or_ne u 0 with h | h
    · subst h
      rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · exact (finrank_span_singleton h).le
  omega

/-- **Trace of the sinc Toeplitz kernel = `n`.** Every diagonal entry is `sinc(θᵢ − θᵢ) = sinc 0 = 1`,
so `Tr (sinc(θᵢ − θⱼ))ᵢⱼ = card ι`. Combined with `sincToeplitz_posSemidef` (all eigenvalues `≥ 0`),
the eigenvalues of the sinc Toeplitz kernel sum to `n` — they average to `1`. RH-free. Axiom-clean. -/
theorem sincToeplitz_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    (Matrix.of (fun i j => Real.sinc (θ i - θ j))).trace = (Fintype.card ι : ℝ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.of_apply, sub_self, Real.sinc_zero]
  simp [Finset.sum_const, Finset.card_univ]

end WeilFluctuationLoewner
end JensenLadder
