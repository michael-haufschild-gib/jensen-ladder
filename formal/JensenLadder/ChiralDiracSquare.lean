import Mathlib

/-!
# Chiral-Dirac determinant perfect-square (RH#13 structural core)

For a chiral (off-diagonal block) operator `D = [[0,B],[C,0]]`, the square is
block-diagonal `D² = [[B·C,0],[0,C·B]]`, so its characteristic determinant
factors and — when `C = Bᴴ` over ℂ — is a PERFECT SQUARE:

  `charpoly(D²) = charpoly(BC)·charpoly(CB) = charpoly(BᴴB)²`  (via `charpoly_mul_comm`).

This is the operator-level reason the squared-variable carrier target `det(D²−w)=−ξ̂²`
is a perfect square with positivity free (`BᴴB ⪰ 0`): real-rootedness is structural,
not assumed. Working note: `docs/rh/what_if_rabbit_holes_20260614.md` RH#13.
This is model-class structure, NOT a proof of RH.

Author: Fable, 2026-06-14.  (New Fable-owned file; targeted build only.)
-/

namespace JensenLadder.ChiralDiracSquare

open Matrix
open scoped ComplexOrder

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The square of a chiral (off-diagonal) block matrix is block-diagonal. -/
lemma chiral_sq (B C : Matrix (Fin n) (Fin n) R) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) R) B C 0) * (fromBlocks 0 B C 0)
      = fromBlocks (B * C) 0 0 (C * B) := by
  rw [fromBlocks_multiply]
  simp

/-- Characteristic polynomial of the chiral square factors into the two blocks'
characteristic polynomials. -/
lemma charpoly_chiral_sq (B C : Matrix (Fin n) (Fin n) R) :
    ((fromBlocks (0 : Matrix (Fin n) (Fin n) R) B C 0) * (fromBlocks 0 B C 0)).charpoly
      = (B * C).charpoly * (C * B).charpoly := by
  rw [chiral_sq, charpoly_fromBlocks_zero₁₂]

/-- **Perfect square (chiral / Hermitian over ℂ).** For `D = [[0,T],[Tᴴ,0]]`,
`charpoly(D²) = charpoly(TᴴT)²` — the chiral square is a perfect square, and `TᴴT ⪰ 0`,
so its (real) spectrum is non-negative. Reality is structural, not assumed. -/
theorem charpoly_chiral_sq_perfect (T : Matrix (Fin n) (Fin n) ℂ) :
    ((fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) T Tᴴ 0)
        * (fromBlocks 0 T Tᴴ 0)).charpoly
      = ((Tᴴ * T).charpoly) ^ 2 := by
  rw [charpoly_chiral_sq]
  rw [charpoly_mul_comm T Tᴴ]    -- (T*Tᴴ).charpoly = (Tᴴ*T).charpoly
  ring

/-- **Reality is structural in the squared variable (RH#25 off-line obstruction).**
If `γ² = r` for a nonnegative real `r` — e.g. `r` an eigenvalue of the PSD
self-adjoint `TᴴT`, which by `charpoly_chiral_sq_perfect` is exactly the spectrum
of the chiral square `D²` — then `γ` is real. An off-line zero (`γ.im ≠ 0`) would
force a *non-real* eigenvalue of a self-adjoint operator, a contradiction. So in
the `w = γ²` variable, positivity of `TᴴT` ⟹ reality of `γ`; reality is not
assumed. This is model-class structure, NOT a proof of RH. -/
lemma im_eq_zero_of_sq_eq_ofReal_nonneg {γ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hsq : γ ^ 2 = (r : ℂ)) : γ.im = 0 := by
  have hmul : γ * γ = (r : ℂ) := by rw [← sq]; exact hsq
  have him : γ.re * γ.im + γ.im * γ.re = 0 := by
    have := congrArg Complex.im hmul
    simpa [Complex.mul_im] using this
  have hre : γ.re * γ.re - γ.im * γ.im = r := by
    have := congrArg Complex.re hmul
    simpa [Complex.mul_re] using this
  have hprod : γ.re * γ.im = 0 := by linarith
  rcases mul_eq_zero.mp hprod with hh | hh
  · have hle : γ.im * γ.im ≤ 0 := by nlinarith [hre, hr, hh]
    exact mul_self_eq_zero.mp (le_antisymm hle (mul_self_nonneg _))
  · exact hh

/-- **Operator-level off-line obstruction.** If `γ²` equals an eigenvalue of the
positive-semidefinite self-adjoint `TᴴT`, then `γ` is real. The eigenvalues of `TᴴT`
are nonnegative reals (`PosSemidef.eigenvalues_nonneg`), and the squared variable
sends `γ²∈ℝ_{≥0}` to `γ∈ℝ` (`im_eq_zero_of_sq_eq_ofReal_nonneg`). This realizes the
off-line obstruction at the actual operator spectrum: an off-line zero whose `w=γ²`
is an eigenvalue of the self-adjoint `TᴴT` would have to be non-real — impossible.
This is model-class structure, NOT a proof of RH. -/
theorem im_eq_zero_of_sq_eq_eigenvalue {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ)
    (γ : ℂ) (i : Fin m)
    (hγ : γ ^ 2 = (((posSemidef_conjTranspose_mul_self T).1.eigenvalues i : ℝ) : ℂ)) :
    γ.im = 0 := by
  have hnn : 0 ≤ (posSemidef_conjTranspose_mul_self T).1.eigenvalues i :=
    (posSemidef_conjTranspose_mul_self T).eigenvalues_nonneg i
  exact im_eq_zero_of_sq_eq_ofReal_nonneg hnn hγ

/-- **RH#26 forward direction (Hamburger), formalized.** The Hankel matrix of the power-sum moments
`m_{i+j} = Σ_l x_l^{i+j}` of a REAL vector `x` is positive-semidefinite — because it is the Gram
matrix `VᴴV` with `V l i = x_l^i`. This is exactly why `RH ⟹ Hankel-PSD`: the carrier moments
`m_k = Σ 1/γ_n^{2k}` come from real `x_l = 1/γ_n²`, so their Hankel matrix is PSD. Realness is the
load-bearing hypothesis — for complex (off-line) `x_l` the conjugation is lost and PSD can fail
(cf. `scripts/research/hilbertPolya/hankel_offline_sensitivity.py`). Model-class structure, NOT a
proof of RH. -/
theorem moment_hankel_posSemidef {N M : ℕ} (x : Fin N → ℝ) :
    (Matrix.of (fun i j : Fin M => ∑ l : Fin N, (x l) ^ ((i : ℕ) + (j : ℕ)))).PosSemidef := by
  set V : Matrix (Fin N) (Fin M) ℝ := Matrix.of (fun l i => (x l) ^ (i : ℕ)) with hV
  have hM : (Matrix.of (fun i j : Fin M => ∑ l : Fin N, (x l) ^ ((i : ℕ) + (j : ℕ))))
      = Vᴴ * V := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hV, Matrix.of_apply,
               star_trivial, pow_add]
  rw [hM]
  exact posSemidef_conjTranspose_mul_self V

/-- **Deninger consumer core:** a skew-adjoint complex matrix has purely-imaginary spectrum.
If `Aᴴ = -A` and `A v = μ v` with `v ≠ 0`, then `Re μ = 0`. In the Deninger/Hilbert–Pólya picture
the normalized generator `Θ−½` is skew-adjoint for the polarization, so every spectral zero satisfies
`Re ρ = ½` (the critical line). Reality of the polarization is the open input; this is the exact
deduction once it holds. Complementary to `im_eq_zero_of_sq_eq_eigenvalue` (the PSD/self-adjoint
direction). This is model-class structure, NOT a proof of RH. -/
theorem skewAdjoint_eigenvalue_re_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : Aᴴ = -A) (μ : ℂ) (v : Fin N → ℂ) (hv : v ≠ 0)
    (hev : A *ᵥ v = μ • v) : μ.re = 0 := by
  have hq : star v ⬝ᵥ A *ᵥ v = μ * (star v ⬝ᵥ v) := by
    rw [hev]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have hstar : star (star v ⬝ᵥ A *ᵥ v) = - (star v ⬝ᵥ A *ᵥ v) := by
    have e1 : star (star v ⬝ᵥ A *ᵥ v) = star (A *ᵥ v) ⬝ᵥ v := by
      conv_lhs => rw [star_dotProduct v (A *ᵥ v), star_star]
    rw [e1, star_mulVec, ← dotProduct_mulVec, hA, neg_mulVec, dotProduct_neg]
  have hqre : (star v ⬝ᵥ A *ᵥ v).re = 0 := by
    have hsum : (star v ⬝ᵥ A *ᵥ v) + (starRingEnd ℂ) (star v ⬝ᵥ A *ᵥ v) = 0 := by
      have : (starRingEnd ℂ) (star v ⬝ᵥ A *ᵥ v) = star (star v ⬝ᵥ A *ᵥ v) := rfl
      rw [this, hstar]; ring
    rw [Complex.add_conj] at hsum
    have h2 : (2 : ℝ) * (star v ⬝ᵥ A *ᵥ v).re = 0 := Complex.ofReal_eq_zero.mp hsum
    linarith
  have hnv_eq : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [dotProduct, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  have hnv_im : (star v ⬝ᵥ v).im = 0 := by rw [hnv_eq]; simp
  have hnv_pos : 0 < (star v ⬝ᵥ v).re := by
    rw [hnv_eq, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact Complex.normSq_pos.mpr (by simpa using hi)
  have hmulre : (μ * (star v ⬝ᵥ v)).re = μ.re * (star v ⬝ᵥ v).re := by
    rw [Complex.mul_re, hnv_im]; ring
  rw [hq, hmulre] at hqre
  rcases mul_eq_zero.mp hqre with h | h
  · exact h
  · exact absurd h (ne_of_gt hnv_pos)

/-- **Deninger polarization consumer (pseudo-Hermitian / RH#27 metric form).** A generator that is
skew-adjoint with respect to a POSITIVE metric `η` has purely-imaginary spectrum. If `η` is
positive-definite, `Aᴴ η = -(η A)` (i.e. `A` is `η`-skew-adjoint), and `A v = μ v` with `v ≠ 0`,
then `Re μ = 0`. This is the actual Deninger polarization hypothesis — the normalized flow is *unitary
for the polarization `η`*, equivalently the generator is `η`-skew-adjoint — and the pseudo-Hermitian (RH#27)
form: reality of the spectrum comes from a positive metric, not from self-adjointness in the standard
inner product. Generalizes `skewAdjoint_eigenvalue_re_zero` (the `η = 1` case). The proof uses that
`η A` is genuinely skew-adjoint (`(η A)ᴴ = Aᴴ η = -(η A)` via `η` Hermitian), so `⟨v, η A v⟩` is
purely imaginary, while `⟨v, η v⟩ > 0` is real (`η` positive-definite). This is model-class structure,
NOT a proof of RH; the open object is the construction of the carrier/polarization, not this deduction. -/
theorem pseudoSkewAdjoint_eigenvalue_re_zero {N : ℕ} (A η : Matrix (Fin N) (Fin N) ℂ)
    (hη : η.PosDef) (hskew : Aᴴ * η = -(η * A)) (μ : ℂ) (v : Fin N → ℂ) (hv : v ≠ 0)
    (hev : A *ᵥ v = μ • v) : μ.re = 0 := by
  have hMs : (η * A)ᴴ = -(η * A) := by
    rw [conjTranspose_mul, hη.1, hskew]
  have hstar : star (star v ⬝ᵥ (η * A) *ᵥ v) = - (star v ⬝ᵥ (η * A) *ᵥ v) := by
    have e1 : star (star v ⬝ᵥ (η * A) *ᵥ v) = star ((η * A) *ᵥ v) ⬝ᵥ v := by
      conv_lhs => rw [star_dotProduct v ((η * A) *ᵥ v), star_star]
    rw [e1, star_mulVec, ← dotProduct_mulVec, hMs, neg_mulVec, dotProduct_neg]
  have hqre : (star v ⬝ᵥ (η * A) *ᵥ v).re = 0 := by
    have hsum : (star v ⬝ᵥ (η * A) *ᵥ v) + (starRingEnd ℂ) (star v ⬝ᵥ (η * A) *ᵥ v) = 0 := by
      have h : (starRingEnd ℂ) (star v ⬝ᵥ (η * A) *ᵥ v) = star (star v ⬝ᵥ (η * A) *ᵥ v) := rfl
      rw [h, hstar]; ring
    rw [Complex.add_conj] at hsum
    have h2 : (2 : ℝ) * (star v ⬝ᵥ (η * A) *ᵥ v).re = 0 := Complex.ofReal_eq_zero.mp hsum
    linarith
  have hMv : (η * A) *ᵥ v = μ • (η *ᵥ v) := by
    rw [← mulVec_mulVec, hev, mulVec_smul]
  have hq : star v ⬝ᵥ (η * A) *ᵥ v = μ * (star v ⬝ᵥ η *ᵥ v) := by
    rw [hMv]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have hnv_pos : 0 < (star v ⬝ᵥ η *ᵥ v).re := by
    have := hη.re_dotProduct_pos hv; simpa using this
  have hnv_im : (star v ⬝ᵥ η *ᵥ v).im = 0 := by
    have e2 : star (star v ⬝ᵥ η *ᵥ v) = star v ⬝ᵥ η *ᵥ v := by
      conv_lhs => rw [star_dotProduct v (η *ᵥ v), star_star]
      rw [star_mulVec, ← dotProduct_mulVec, hη.1]
    have h := congrArg Complex.im e2
    rw [show star (star v ⬝ᵥ η *ᵥ v) = (starRingEnd ℂ) (star v ⬝ᵥ η *ᵥ v) from rfl,
        Complex.conj_im] at h
    linarith
  have hmulre : (μ * (star v ⬝ᵥ η *ᵥ v)).re = μ.re * (star v ⬝ᵥ η *ᵥ v).re := by
    rw [Complex.mul_re, hnv_im]; ring
  rw [hq, hmulre] at hqre
  rcases mul_eq_zero.mp hqre with h | h
  · exact h
  · exact absurd h (ne_of_gt hnv_pos)

end JensenLadder.ChiralDiracSquare
