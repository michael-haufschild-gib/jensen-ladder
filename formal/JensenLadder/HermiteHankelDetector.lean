import Mathlib
import JensenLadder.SecularGroundState

/-!
# Hermite–Hankel off-line-zero detector (real-root Hankel positivity)

The faithful (signed) secular reconstruction of the CCM route is governed by the **companion matrix**
`C = diag(d) − u·1ᵀ` (a rank-one update of the real grid `diag(d)` by the signed source `u`), whose
eigenvalues are exactly the secular roots `S(z) = ∑ₖ uₖ/(dₖ − z) = 1` (matrix determinant lemma).
Because `C` is **real**, its non-real eigenvalues come in conjugate pairs, so the faithful integer
`κ₋ = #{off-line roots}` is modeled at finite scale by the count of non-real eigenvalues of `C`.

**Hermite's theorem** counts real roots by the signature of the Hankel matrix of Newton power-sums
`sₘ = tr(Cᵐ) = ∑ⱼ ρⱼᵐ`: for distinct roots, `#real = signature(H)`, `H_{ik} = s_{i+k}`, hence
`κ₋ = n − signature(H)`. Numerically refereed (mpmath, dps=60) across positive / signed / near-`(−1)ⁿ`
sources and random signed trials: the identity `κ₋ = n − sig(H)` holds with zero failures, and the
entries reproduce the closed-form traces `tr(C) = ∑d − ∑u`, `tr(C²) = ∑d² − 2∑du + (∑u)²`
in those finite tests.

This file formalizes the **RH-free easy half of Hermite** — the side that yields a *detector*:

* `hankel_powerSum_posSemidef` — for ANY real roots `r`, the power-sum Hankel `H_{ik} = ∑ⱼ rⱼ^{i+k}` is
  positive semidefinite, because `H = ∑ⱼ vⱼ vⱼᵀ` with `vⱼ = (1, rⱼ, …, rⱼⁿ⁻¹)` is a sum of rank-one
  PSD outer products (`vecMulVec_self_posSemidef` + `Finset.sum_induction` of `PosSemidef.add`).
* `hankel_trace_pow_posSemidef` — the **PT-unbroken** corollary: if `C` is real-diagonalizable
  (`C = P·diag(r)·P⁻¹`, real `r`), then the Hankel of `tr(Cᵐ)` is PSD (`tr(Cᵐ) = ∑ⱼ rⱼᵐ` by trace
  cyclicity + `diagonal_pow`).

**Contrapositive = the detector.** If the trace-Hankel `H = (tr(Cⁱ⁺ᵏ))` is *not* PSD, then `C` is **not**
real-diagonalizable. In the intended simple-root companion setting, failure of real diagonalizability is the
finite off-line-root certificate; without that hypothesis, the theorem itself only certifies failure of the
PT-unbroken/real-diagonalizable condition. Thus a single PSD failure of an explicit, root-free,
trace-computable matrix is a finite falsifier for that condition. This is a third detector alongside
hawking's off-line Li detector (`OfflineLiDetector`) and
berry's `{Φ≤0}` localization (`complex_root_in_Phi_nonpos`); unlike those, its target is a **PSD test**,
so it is exactly what the Schur-complement machinery of `SecularGroundState`
(`schur_posDef_iff` / `schur_posSemidef_iff`, §55/§56) certifies block-locally as the cutoff grows.

This is the *easy* Hermite direction (real roots ⟹ Hankel PSD), giving a sufficient
condition for detecting off-line zeros by Hankel-PSD failure. It is not a proof of RH: the RH-strength
content is the converse half (`H ≻ 0 ⟹ all real`) together with uniform persistence of `H ≻ 0` as the
prime cutoff `λ → ∞` (= the no-margin / De Bruijn–Newman `Λ = 0` wall). RH-free. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace JensenLadder
namespace HermiteHankelDetector

open Matrix
open JensenLadder.SecularGroundState

/-- **Power-sum Hankel of real roots is positive semidefinite (easy Hermite half).** Given real "roots"
`r : ρ → ℝ` (any finite index `ρ`), the `n×n` Hankel matrix `H_{ik} = ∑ⱼ (rⱼ)^{i+k}` of their Newton
power sums `sₘ = ∑ⱼ rⱼᵐ` is positive semidefinite. Reason: `H = ∑ⱼ vⱼ vⱼᵀ` with the Vandermonde column
`vⱼ = (1, rⱼ, …, rⱼⁿ⁻¹)`, a finite sum of rank-one PSD outer products. RH-free. Axiom-clean. -/
theorem hankel_powerSum_posSemidef {ρ : Type*} [Fintype ρ] (n : ℕ) (r : ρ → ℝ) :
    (Matrix.of (fun i k : Fin n => ∑ j, (r j) ^ ((i : ℕ) + (k : ℕ)))).PosSemidef := by
  have hEq : (Matrix.of (fun i k : Fin n => ∑ j, (r j) ^ ((i : ℕ) + (k : ℕ))))
      = ∑ j, Matrix.vecMulVec (fun i : Fin n => (r j) ^ (i : ℕ)) (fun i : Fin n => (r j) ^ (i : ℕ)) := by
    ext i k
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [pow_add])
  rw [hEq]
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) (fun j _ => vecMulVec_self_posSemidef _)

/-- **PT-unbroken ⟹ trace-Hankel PSD (the detector's positive side).** If the companion `C` is
real-diagonalizable, `C = P·diag(r)·P⁻¹` with real eigenvalues `r` and invertible `P`, then the Hankel
matrix of its trace power-sums `H_{ik} = tr(Cⁱ⁺ᵏ)` is positive semidefinite. Proof: `Cᵐ = P·diag(r)ᵐ·P⁻¹`
(induction, `P⁻¹P = 1`), so by trace cyclicity `tr(Cᵐ) = tr(diag(rᵐ)) = ∑ⱼ rⱼᵐ`, reducing to
`hankel_powerSum_posSemidef`. Contrapositive: a PSD failure of `(tr(Cⁱ⁺ᵏ))` certifies failure of
real diagonalizability; in the simple-root companion setting this is the finite off-line-root certificate.
RH-free. Axiom-clean. -/
theorem hankel_trace_pow_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (C P : Matrix ι ι ℝ) (r : ι → ℝ) (hP : IsUnit P.det)
    (hdiag : C = P * Matrix.diagonal r * P⁻¹) :
    (Matrix.of (fun i k : Fin n => (C ^ ((i : ℕ) + (k : ℕ))).trace)).PosSemidef := by
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hCm : ∀ m : ℕ, C ^ m = P * (Matrix.diagonal r) ^ m * P⁻¹ := by
    intro m
    induction m with
    | zero => simp [Matrix.mul_nonsing_inv P hP]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, hdiag,
          show P * Matrix.diagonal r ^ k * P⁻¹ * (P * Matrix.diagonal r * P⁻¹)
            = P * Matrix.diagonal r ^ k * (P⁻¹ * P) * Matrix.diagonal r * P⁻¹ by noncomm_ring,
          hPP, Matrix.mul_one]
      noncomm_ring
  have htr : ∀ m : ℕ, (C ^ m).trace = ∑ j, (r j) ^ m := by
    intro m
    rw [hCm, Matrix.diagonal_pow, Matrix.trace_mul_cycle, hPP, Matrix.one_mul,
        Matrix.trace_diagonal]
    simp [Pi.pow_apply]
  have hEq : (Matrix.of (fun i k : Fin n => (C ^ ((i : ℕ) + (k : ℕ))).trace))
      = (Matrix.of (fun i k : Fin n => ∑ j, (r j) ^ ((i : ℕ) + (k : ℕ)))) := by
    ext i k; simp only [Matrix.of_apply]; exact htr _
  rw [hEq]
  exact hankel_powerSum_posSemidef n r

/-- **Signed-residue Gram positivity (the Bezoutian/residue mechanism).** A weighted Gram
`H = ∑ⱼ wⱼ · (vⱼ vⱼᵀ)` with **nonnegative** weights `wⱼ ≥ 0` is positive semidefinite (each term is a
nonneg multiple of a rank-one PSD outer product). This is the abstract core of the Hermite–Biehler /
Bezoutian mechanism: the Bezoutian of `A` (distinct real roots `αⱼ`) and `B` is congruent to
`∑ⱼ rⱼ · (vⱼ vⱼᵀ)` with `vⱼ` the Vandermonde column at `αⱼ` and `rⱼ = B(αⱼ)/A'(αⱼ)` the partial-fraction
residue; so **all residues `≥ 0` ⟹ Bezoutian PSD ⟹ (with interlacing) real spectrum**. Generalizes
`hankel_powerSum_posSemidef` (the `wⱼ ≡ 1` case). RH-free. Axiom-clean. -/
theorem weighted_gram_posSemidef {ρ : Type*} [Fintype ρ] {n : ℕ}
    (w : ρ → ℝ) (v : ρ → (Fin n → ℝ)) (hw : ∀ j, 0 ≤ w j) :
    (∑ j, w j • Matrix.vecMulVec (v j) (v j)).PosSemidef :=
  Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun j _ => (vecMulVec_self_posSemidef (v j)).smul (hw j))

/-- **Negative-residue region is where PSD failure can occur (contrapositive).** If a signed-residue Gram
`∑ⱼ wⱼ·(vⱼ vⱼᵀ)` **fails** to be positive semidefinite, then **some residue is strictly negative**.
Equivalently: a PSD failure in the Bezoutian/Hankel test can only come from a sign-changing source.
In the intended simple-root companion setting that failure is the off-line-root detector. This is the Lean form of berry's
`complex_root_in_Phi_nonpos` (complex secular roots confined to the negative-residue `{Φ≤0}` region) and
of hawking's 2577 mechanism (the primes break Perron–Frobenius positivity, *forcing* the alternation
that is the only possible seat of an off-line zero). RH-free. Axiom-clean. -/
theorem neg_residue_of_gram_not_posSemidef {ρ : Type*} [Fintype ρ] {n : ℕ}
    (w : ρ → ℝ) (v : ρ → (Fin n → ℝ))
    (h : ¬ (∑ j, w j • Matrix.vecMulVec (v j) (v j)).PosSemidef) :
    ∃ j, w j < 0 := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  exact h (weighted_gram_posSemidef w v hc)

/-- **Signed-residue Gram positivity is EXACTLY residue-nonnegativity (the iff, on a regular node set).**
When the nodes give an **invertible Vandermonde** `W` (`Wᵢⱼ = vⱼ(i)`, i.e. the rank-one directions `vⱼ`
are linearly independent — the generic/distinct-node case), the signed Gram `H = ∑ⱼ wⱼ·(vⱼ vⱼᵀ)` is
positive semidefinite **iff every weight `wⱼ ≥ 0`**. Proof: `H = W·diag(w)·Wᵀ` is a *congruence* of
`diag(w)` by the invertible `Wᵀ` (`(Wᵀ)ᴴ = W` over ℝ), so `posSemidef_conj_iff` (SecularGroundState §44)
reduces `H ⪰ 0` to `diag(w) ⪰ 0 ⟺ ∀ j, 0 ≤ wⱼ` (`Matrix.posSemidef_diagonal_iff`). This upgrades
`weighted_gram_posSemidef` from one direction to a full equivalence.

For the Bezoutian `Bez(A,B)` of a polynomial `A` with distinct real roots (the invertible-Vandermonde
case) congruent to `∑ⱼ rⱼ·(vⱼ vⱼᵀ)` with `rⱼ = B(αⱼ)/A'(αⱼ)`: **`Bez(A,B) ⪰ 0 ⟺ all residues `rⱼ ≥ 0`**
— i.e. the Hermite–Biehler positivity is *precisely* residue-sign-definiteness. The two remaining
classical pieces for the full polynomial statement are the Bezoutian = `∑ rⱼ vⱼvⱼᵀ` Vandermonde identity
and `residues-same-sign ⟺ interlacing` (Hermite–Kronecker). RH-free. Axiom-clean. -/
theorem weighted_gram_posSemidef_iff {n : ℕ} (w : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (hV : IsUnit (Matrix.of (fun i j : Fin n => v j i)).det) :
    (∑ j, w j • Matrix.vecMulVec (v j) (v j)).PosSemidef ↔ ∀ j, 0 ≤ w j := by
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j : Fin n => v j i) with hW
  have hsum : (∑ j, w j • Matrix.vecMulVec (v j) (v j)) = W * Matrix.diagonal w * Wᵀ := by
    ext i k
    rw [Matrix.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, hW]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have hWT : (Wᵀ)ᴴ = W := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hWTdet : IsUnit (Wᵀ).det := by rw [Matrix.det_transpose]; exact hV
  rw [hsum, show W * Matrix.diagonal w * Wᵀ = (Wᵀ)ᴴ * Matrix.diagonal w * Wᵀ by rw [hWT],
      posSemidef_conj_iff hWTdet, Matrix.posSemidef_diagonal_iff]

/-- **Truncated moment matrix of a signed atomic measure is PSD ⟺ the measure is positive.** For
**distinct** real nodes `αⱼ` (`α` injective) and real weights `rⱼ`, the moment matrix of the discrete
measure `μ = ∑ⱼ rⱼ δ_{αⱼ}`,
`M_{ik} = ∫ x^{i+k} dμ = ∑ⱼ rⱼ · αⱼ^{i+k}`,
is positive semidefinite **iff every weight `rⱼ ≥ 0`** (i.e. `μ ≥ 0`). Proof: `M = ∑ⱼ rⱼ·(vⱼ vⱼᵀ)` with
`vⱼ = (1, αⱼ, …, αⱼⁿ⁻¹)`, the node matrix is the (transposed) **Vandermonde** which is invertible exactly
because the `αⱼ` are distinct (`Matrix.det_vandermonde_ne_zero_iff`), so `weighted_gram_posSemidef_iff`
applies. This is the finite **truncated Hamburger moment problem** for atomic measures, and the
moment-problem face of the Bezoutian/Hankel positivity: the secular/Bezoutian PSD test reads off
**positivity of the underlying (signed) spectral measure**. RH-free. Axiom-clean. -/
theorem moment_matrix_posSemidef_iff {n : ℕ} (α : Fin n → ℝ) (r : Fin n → ℝ)
    (hα : Function.Injective α) :
    (Matrix.of (fun i k : Fin n => ∑ j, r j * (α j) ^ ((i : ℕ) + (k : ℕ)))).PosSemidef
      ↔ ∀ j, 0 ≤ r j := by
  have hM : (Matrix.of (fun i k : Fin n => ∑ j, r j * (α j) ^ ((i : ℕ) + (k : ℕ))))
      = ∑ j, r j • Matrix.vecMulVec (fun i : Fin n => (α j) ^ (i : ℕ))
          (fun i : Fin n => (α j) ^ (i : ℕ)) := by
    ext i k
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [pow_add])
  rw [hM]
  refine weighted_gram_posSemidef_iff r (fun j i => (α j) ^ (i : ℕ)) ?_
  have hWeq : (Matrix.of (fun i j : Fin n => (α j) ^ (i : ℕ))) = (Matrix.vandermonde α)ᵀ := by
    ext i j; simp [Matrix.vandermonde_apply, Matrix.transpose_apply]
  rw [hWeq, Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hα)

/-- **Cofactor / partial-fraction decomposition (first step of the polynomial Bezoutian).** For
**distinct** real nodes `αⱼ` and a polynomial `B` of degree `< n`,
`B = ∑ⱼ rⱼ · Aⱼ`,  with  `Aⱼ = ∏_{k≠j}(X − αₖ)`  the cofactor and  `rⱼ = B(αⱼ) / ∏_{k≠j}(αⱼ − αₖ) =
B(αⱼ)/A'(αⱼ)`  the **partial-fraction residue** of `B/A` at `αⱼ` (`A = ∏(X−αₖ)`). This is the residue
representation that drives the Bezoutian identity `Bez(A,B)(s,t) = ∑ⱼ rⱼ Aⱼ(s)Aⱼ(t)` (because
`A(s)Aⱼ(t) − A(t)Aⱼ(s) = (s−t)Aⱼ(s)Aⱼ(t)`), hence `Bez(A,B) = ∑ⱼ rⱼ·(wⱼ wⱼᵀ)` with `wⱼ = coeffs(Aⱼ)`;
the `wⱼ` are linearly independent (cofactor basis), so `weighted_gram_posSemidef_iff` then gives
**Bezoutian PSD ⟺ all residues `rⱼ ≥ 0`**. Proven from Mathlib's `Lagrange.eq_interpolate` (`B` equals
its Lagrange interpolant on the nodes) + the basis-divisor product. RH-free. Axiom-clean.

This is the analytic heart of the scoped `bezoutian_definite_iff_interlacing` (worklog §59–§62); the
remaining classical steps are the bivariate Bezoutian identity above (matrix-coefficient extraction) and
`residues-same-sign ⟺ interlacing` (Hermite–Kronecker). -/
theorem cofactor_decomposition {n : ℕ} (α : Fin n → ℝ) (B : Polynomial ℝ)
    (hα : Function.Injective α) (hB : B.degree < (n : ℕ)) :
    B = ∑ j, (B.eval (α j) / ∏ k ∈ Finset.univ.erase j, (α j - α k)) •
            ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k)) := by
  have hdeg : B.degree < ((Finset.univ : Finset (Fin n)).card : ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]; exact hB
  have hinj : Set.InjOn α (Finset.univ : Finset (Fin n)) := hα.injOn
  have hbd : ∀ a b : ℝ, Lagrange.basisDivisor a b = Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C b) := by
    intro a b; unfold Lagrange.basisDivisor; ring_nf
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hbasis : Lagrange.basis Finset.univ α j
      = Polynomial.C ((∏ k ∈ Finset.univ.erase j, (α j - α k))⁻¹)
        * ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k)) := by
    rw [Lagrange.basis, Finset.prod_congr rfl (fun k _ => hbd (α j) (α k)),
        Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_inv_distrib]
  rw [hbasis, Polynomial.smul_eq_C_mul, div_eq_mul_inv, map_mul, mul_assoc]

/-- **Cofactor polynomials are linearly independent (Bezoutian brick, piece (b)).** For distinct real
nodes `αⱼ`, the family of cofactors `Aⱼ = ∏_{k≠j}(X − αₖ)` is linearly independent over `ℝ`. Proof: if
`∑ⱼ cⱼ Aⱼ = 0`, evaluate at `αₘ`; since `Aⱼ(αₘ) = ∏_{k≠j}(αₘ − αₖ)` vanishes for `j ≠ m` (the `k = m`
factor is `0`) and is `∏_{k≠m}(αₘ − αₖ) ≠ 0` for `j = m`, only the `m`-th term survives, forcing
`cₘ = 0`. Equivalently the **cofactor coefficient matrix is invertible** — the linear-independence
hypothesis that `weighted_gram_posSemidef_iff` needs to read the Bezoutian `∑ⱼ rⱼ·(wⱼ wⱼᵀ)` (`wⱼ =
coeffs Aⱼ`) as a *regular* signed Gram. RH-free. Axiom-clean. -/
theorem cofactor_linearIndependent {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α) :
    LinearIndependent ℝ
      (fun j : Fin n => ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have heval := congrArg (Polynomial.eval (α m)) hc
  rw [Polynomial.eval_finsetSum, Polynomial.eval_zero] at heval
  have key : ∀ j : Fin n,
      (c j • ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).eval (α m)
        = c j * ∏ k ∈ Finset.univ.erase j, (α m - α k) := by
    intro j
    rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod]
    congr 1
    exact Finset.prod_congr rfl
      (fun k _ => by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
  rw [Finset.sum_congr rfl (fun j _ => key j)] at heval
  rw [Finset.sum_eq_single m] at heval
  · have hprod : (∏ k ∈ Finset.univ.erase m, (α m - α k)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      simp only [Finset.mem_erase] at hk
      exact sub_ne_zero.mpr (fun h => hk.1 (hα h.symm))
    exact (mul_eq_zero.mp heval).resolve_right hprod
  · intro j _ hjm
    have hz : (∏ k ∈ Finset.univ.erase j, (α m - α k)) = 0 := by
      apply Finset.prod_eq_zero (i := m)
      · rw [Finset.mem_erase]; exact ⟨fun h => hjm h.symm, Finset.mem_univ m⟩
      · ring
    rw [hz, mul_zero]
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-- **Cofactor coefficient matrix is invertible (Bezoutian brick, piece (b), matrix form).** For distinct
real nodes `αⱼ`, the matrix `M_{ij} = coeff_i(Aⱼ)`, `Aⱼ = ∏_{k≠j}(X − αₖ)`, has a unit determinant.
Proof: the **Vandermonde × cofactor-coefficient** product is diagonal — `(V·M)_{lj} = ∑ᵢ αₗⁱ·coeff_i(Aⱼ)
= Aⱼ(αₗ)` (`eval_eq_sum_range'`, `deg Aⱼ = n−1 < n`), and `Aⱼ(αₗ) = ∏_{k≠j}(αₗ − αₖ)` vanishes for `l≠j`
(the `k=l` factor) and is `≠0` for `l=j` — so `V·M = diag(A'(αⱼ))`. Both `V` (`det_vandermonde_ne_zero_iff`)
and the diagonal are invertible, forcing `det M ≠ 0`. This is exactly the invertibility
`weighted_gram_posSemidef_iff` requires to read the cofactor Gram as regular. RH-free. Axiom-clean. -/
theorem cofactor_coeff_matrix_isUnit {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α) :
    IsUnit (Matrix.of (fun i j : Fin n =>
      (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))).det := by
  set A : Fin n → Polynomial ℝ :=
    fun j => ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k)) with hA
  have hdeg : ∀ j, (A j).natDegree < n := by
    intro j
    have hn : 0 < n := Fin.pos j
    have hcard : (A j).natDegree = (Finset.univ.erase j).card := by
      simp only [hA]
      rw [Polynomial.natDegree_prod _ _ (fun k _ => Polynomial.X_sub_C_ne_zero (α k))]
      simp
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega
  have heval : ∀ l j : Fin n,
      (∑ i : Fin n, (α l) ^ (i : ℕ) * (A j).coeff (i : ℕ)) = (A j).eval (α l) := by
    intro l j
    rw [Polynomial.eval_eq_sum_range' (hdeg j) (α l),
        Fin.sum_univ_eq_sum_range (fun i => (α l) ^ i * (A j).coeff i) n]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hVM : (Matrix.vandermonde α) * (Matrix.of (fun (i : Fin n) (j : Fin n) => (A j).coeff (i : ℕ)))
      = Matrix.diagonal (fun j => (A j).eval (α j)) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [Matrix.vandermonde_apply, Matrix.of_apply]
    rw [heval l j]
    by_cases hlj : l = j
    · subst hlj; simp
    · rw [if_neg hlj]
      simp only [hA, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)
      simp
  have hdiagdet : (Matrix.diagonal (fun j => (A j).eval (α j))).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro j _
    simp only [hA, Polynomial.eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hα h.symm))
  have hmul : (Matrix.vandermonde α).det
      * (Matrix.of (fun (i : Fin n) (j : Fin n) => (A j).coeff (i : ℕ))).det ≠ 0 := by
    rw [← Matrix.det_mul, hVM]; exact hdiagdet
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hmul)

/-- Coefficient vector of the cofactor polynomial
`Aⱼ = ∏_{k≠j} (X - αₖ)`, truncated to `Fin n`. Naming this vector keeps the
cofactor-Gram specializations below from re-elaborating the full polynomial
product twice in every theorem header. -/
noncomputable def cofactorCoeffVec {n : ℕ} (α : Fin n → ℝ) (j : Fin n) : Fin n → ℝ :=
  fun i => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ)

theorem cofactor_coeff_matrix_isUnit_vec {n : ℕ} (α : Fin n → ℝ)
    (hα : Function.Injective α) :
    IsUnit (Matrix.of (fun i j : Fin n => cofactorCoeffVec α j i)).det := by
  simpa [cofactorCoeffVec] using cofactor_coeff_matrix_isUnit α hα

set_option maxHeartbeats 4000000 in
/-- **Cofactor-Gram (= Bezoutian) positivity ⟺ residue-sign-definiteness — MILESTONE.** Combining the
inertia core `weighted_gram_posSemidef_iff` (§61) with the cofactor-matrix invertibility
(`cofactor_coeff_matrix_isUnit`), the **cofactor Gram** `∑ⱼ rⱼ·(wⱼ wⱼᵀ)` with `wⱼ = coeffs(Aⱼ)`,
`Aⱼ = ∏_{k≠j}(X − αₖ)` (distinct nodes), is positive semidefinite **iff every residue `rⱼ ≥ 0`**. Since
the Bezoutian `Bez(A,B)` equals this cofactor Gram with `rⱼ = B(αⱼ)/A'(αⱼ)` (the bivariate identity
`Bez(s,t)=∑ⱼ rⱼ Aⱼ(s)Aⱼ(t)`, with `B = ∑ⱼ rⱼ Aⱼ` from `cofactor_decomposition`), this **is** the
residue-sign form of Hermite–Biehler positivity: `Bezoutian PSD ⟺ all residues ≥ 0`. The remaining gap to
the *literal* coefficient-Bezoutian matrix is only the bivariate→matrix identity (worklog §59–§64 piece
(a)). RH-free. Axiom-clean. -/
theorem cofactor_gram_posSemidef_iff {n : ℕ} (α : Fin n → ℝ) (r : Fin n → ℝ)
    (hα : Function.Injective α) :
    (∑ j, r j • Matrix.vecMulVec
        (fun i : Fin n => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))
        (fun i : Fin n => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))).PosSemidef
      ↔ ∀ j, 0 ≤ r j :=
  weighted_gram_posSemidef_iff r
    (fun j i => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))
    (cofactor_coeff_matrix_isUnit α hα)

/-- **Signed-residue Gram positive-DEFINITENESS is EXACTLY strict residue-positivity (PD iff).** On a
regular node set (invertible Vandermonde `W`), the signed Gram `∑ⱼ wⱼ·(vⱼ vⱼᵀ)` is positive *definite*
**iff every weight `wⱼ > 0`** — the strict analog of `weighted_gram_posSemidef_iff`, via the same
congruence `W·diag(w)·Wᵀ` with `posDef_conj_iff` (§53) + `Matrix.posDef_diagonal_iff`. RH-free.
Axiom-clean. -/
theorem weighted_gram_posDef_iff {n : ℕ} (w : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (hV : IsUnit (Matrix.of (fun i j : Fin n => v j i)).det) :
    (∑ j, w j • Matrix.vecMulVec (v j) (v j)).PosDef ↔ ∀ j, 0 < w j := by
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j : Fin n => v j i) with hW
  have hsum : (∑ j, w j • Matrix.vecMulVec (v j) (v j)) = W * Matrix.diagonal w * Wᵀ := by
    ext i k
    rw [Matrix.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, hW]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have hWT : (Wᵀ)ᴴ = W := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hWTdet : IsUnit (Wᵀ).det := by rw [Matrix.det_transpose]; exact hV
  rw [hsum, show W * Matrix.diagonal w * Wᵀ = (Wᵀ)ᴴ * Matrix.diagonal w * Wᵀ by rw [hWT],
      posDef_conj_iff hWTdet, Matrix.posDef_diagonal_iff]

set_option maxHeartbeats 1000000 in
/-- **Cofactor-Gram (= Bezoutian) positive-DEFINITENESS ⟺ strict residue-positivity (strict
Hermite–Biehler).** The cofactor Gram is positive definite iff every residue `rⱼ > 0`. With the
Bezoutian identification (`rⱼ = B(αⱼ)/A'(αⱼ)`), this is **Bezoutian PD ⟺ all residues > 0** — the
*strict* (simple-interlacing) Hermite–Biehler case, complementing the boundary PSD criterion §66.
RH-free. Axiom-clean. -/
theorem cofactor_gram_posDef_iff {n : ℕ} (α : Fin n → ℝ) (r : Fin n → ℝ)
    (hα : Function.Injective α) :
    (∑ j, r j • Matrix.vecMulVec
        (fun i : Fin n => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))
        (fun i : Fin n => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))).PosDef
      ↔ ∀ j, 0 < r j :=
  weighted_gram_posDef_iff r
    (fun j i => (∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α k))).coeff (i : ℕ))
    (cofactor_coeff_matrix_isUnit α hα)

/-- **Bezoutian numerator factors through `(s − t)` (the bivariate identity's heart, piece (a)).** With
`A(x) = ∏ₖ(x − αₖ)` and the cofactor `Aⱼ(x) = ∏_{k≠j}(x − αₖ)`, evaluated at two points `s, t`:
`A(s)·Aⱼ(t) − A(t)·Aⱼ(s) = (s − t)·Aⱼ(s)·Aⱼ(t)`.
Proof: factor `A = (X − αⱼ)·Aⱼ` (`Finset.mul_prod_erase`), substitute, `ring`. This is exactly why the
Bezoutian `Bez(A,B)(s,t) = (A(s)B(t) − A(t)B(s))/(s − t)` is a genuine polynomial (the numerator is
`(s−t)`-divisible) and, summing over `B = ∑ⱼ rⱼ Aⱼ` (`cofactor_decomposition`), why
`Bez(s,t) = ∑ⱼ rⱼ Aⱼ(s) Aⱼ(t)` — whose coefficient matrix is the cofactor Gram `∑ⱼ rⱼ·(wⱼ wⱼᵀ)`
characterized in `cofactor_gram_posSemidef_iff`/`cofactor_gram_posDef_iff`. The one remaining step to the
literal coefficient-Bezoutian is the coefficient extraction from this bivariate identity. RH-free.
Axiom-clean. -/
theorem bezoutian_numerator_factor {n : ℕ} (α : Fin n → ℝ) (j : Fin n) (s t : ℝ) :
    (∏ k, (s - α k)) * (∏ k ∈ Finset.univ.erase j, (t - α k))
      - (∏ k, (t - α k)) * (∏ k ∈ Finset.univ.erase j, (s - α k))
    = (s - t) * (∏ k ∈ Finset.univ.erase j, (s - α k))
        * (∏ k ∈ Finset.univ.erase j, (t - α k)) := by
  have hs : (∏ k, (s - α k)) = (s - α j) * ∏ k ∈ Finset.univ.erase j, (s - α k) :=
    (Finset.mul_prod_erase Finset.univ (fun k => s - α k) (Finset.mem_univ j)).symm
  have ht : (∏ k, (t - α k)) = (t - α j) * ∏ k ∈ Finset.univ.erase j, (t - α k) :=
    (Finset.mul_prod_erase Finset.univ (fun k => t - α k) (Finset.mem_univ j)).symm
  rw [hs, ht]; ring

/-- **Rank of a signed Vandermonde Gram = number of nonzero residues (Hermite rank refinement).** On a
regular node set (invertible Vandermonde `W`), the signed Gram `∑ⱼ wⱼ·(vⱼ vⱼᵀ)` has
`rank = #{j : wⱼ ≠ 0}`. Sharper than the PSD/PD criteria (§66/§67): it pins the **exact rank**, hence the
**kernel dimension `= #{j : wⱼ = 0}`** — the count of vanishing residues, i.e. the degenerate/no-margin
directions. Proof: `rank` is invariant under multiplication by the invertible `W`, `Wᵀ`
(`rank_mul_eq_left/right_of_isUnit_det`), reducing the congruent `W·diag(w)·Wᵀ` to `rank(diag w) =
#{wⱼ≠0}` (`rank_diagonal`). This is the rank/Hermite-signature content of the Bezoutian. RH-free.
Axiom-clean. -/
theorem weighted_gram_rank {n : ℕ} (w : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (hV : IsUnit (Matrix.of (fun i j : Fin n => v j i)).det) :
    (∑ j, w j • Matrix.vecMulVec (v j) (v j)).rank = Fintype.card {j // w j ≠ 0} := by
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j : Fin n => v j i) with hW
  have hsum : (∑ j, w j • Matrix.vecMulVec (v j) (v j)) = W * Matrix.diagonal w * Wᵀ := by
    ext i k
    rw [Matrix.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, hW]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have hWTdet : IsUnit (Wᵀ).det := by rw [Matrix.det_transpose]; exact hV
  have h1 : (W * Matrix.diagonal w * Wᵀ).rank = (W * Matrix.diagonal w).rank :=
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hWTdet
  have h2 : (W * Matrix.diagonal w).rank = (Matrix.diagonal w).rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hV
  rw [hsum, h1, h2, Matrix.rank_diagonal]

set_option maxHeartbeats 4000000 in
/-- **Cofactor-Gram (= Bezoutian) rank = number of nonzero residues.** Specialization of
`weighted_gram_rank` to the cofactor vectors: `rank(Bez(A,B)) = #{j : rⱼ ≠ 0}`, so the **Bezoutian's
nullity equals the number of vanishing residues** — the count of no-margin/degenerate seams. RH-free.
Axiom-clean. -/
theorem cofactor_gram_rank {n : ℕ} (α : Fin n → ℝ) (r : Fin n → ℝ)
    (hα : Function.Injective α) :
    (∑ j, r j • Matrix.vecMulVec (cofactorCoeffVec α j) (cofactorCoeffVec α j)).rank
      = Fintype.card {j // r j ≠ 0} :=
  weighted_gram_rank r
    (cofactorCoeffVec α)
    (cofactor_coeff_matrix_isUnit_vec α hα)

end HermiteHankelDetector
end JensenLadder
