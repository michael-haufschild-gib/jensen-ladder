import Mathlib

/-!
# Krein–Langer negative inertia upper bounds (Stage 1)

`formalization-roadmap-finite-to-apex.md` Stage 1 (exact finite Krein–Langer inertia). The carrier
dichotomy lives in `CarrierPickKernel`/`MeasureCarrier`: a pole in the open upper half-plane (an
off-line zero) breaks Herglotz/Pick-positivity, giving negative inertia `κ₋ ≥ 1`. The matching
**upper bound** — `κ₋ ≤ #{off-line poles}` — is the rank-`k` interlacing fact for quadratic-form
signatures: a form that is positive-semidefinite *up to `k` squares* has at most `k` negative
directions. This file proves that abstract bound for real quadratic forms via mathlib's `sigNeg`
(the maximal finrank of a negative-definite subspace, the uniqueness side of Sylvester's law).

This is the real-quadratic-form core of the `κ₋` count. Specializing it to the complex Hermitian
carrier Pick matrix (the realification `finrank_conjSym` passage) and pinning the exact equality
`κ₋ = #off-line poles` are the remaining Stage-1 bricks; only the **upper bound** is proved here. No
infinite carrier `m_ξ`, no RH.
-/

open QuadraticMap Matrix
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions

noncomputable section

/-- **General Krein–Langer negative-inertia bound (`κ₋ ≤ k`).** A real quadratic form `Q` on a
finite-dimensional space that becomes nonnegative after adding `k` squares of linear functionals
(`0 ≤ Q x + ∑_{i<k} (ℓ_i x)²` for all `x`) has negative inertia `sigNeg Q ≤ k`. Mechanism: on any
negative-definite subspace `V` (where `Q x < 0`), the linear map `x ↦ (ℓ_0 x, …, ℓ_{k-1} x) ∈ ℝ^k` is
injective — if all `ℓ_i x = 0` then `Q x ≥ 0`, contradicting `Q x < 0` — so `V` embeds in `ℝ^k` and
`dim V ≤ k`. This is the carrier statement "at most `k` off-line poles ⟹ at most `k` negative
squares", the upper-bound half of the exact Krein–Langer `κ₋`. -/
theorem sigNeg_le_of_add_sum_sq_nonneg {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) {k : ℕ} (ℓ : Fin k → (M →ₗ[ℝ] ℝ))
    (h : ∀ x, 0 ≤ Q x + ∑ i, (ℓ i x) ^ 2) : sigNeg Q ≤ k := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨V, hVrank, hVneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  set F : M →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi ℓ with hF
  have hinj : Function.Injective (F.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    by_contra hy0
    have hQneg : Q (y : M) < 0 := by
      have hp := hVneg y hy0
      rwa [restrict_apply, QuadraticMap.neg_apply, neg_pos] at hp
    have hall : ∀ i, ℓ i (y : M) = 0 := by
      intro i
      have hi := congrFun hy i
      simpa [hF, LinearMap.domRestrict_apply, LinearMap.pi_apply] using hi
    have hh := h (y : M)
    have hsum : ∑ i, (ℓ i (y : M)) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hall i]; ring)
    rw [hsum, add_zero] at hh
    linarith
  have hle : Module.finrank ℝ V ≤ Module.finrank ℝ (Fin k → ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun ℝ, hVrank] at hle
  omega

/-- **Rank-one Krein–Langer bound (`κ₋ ≤ 1`, the single off-line pole).** A real quadratic form that
is positive-semidefinite up to one square (`0 ≤ Q x + (ℓ x)²`) has at most one negative direction,
`sigNeg Q ≤ 1`. The `k = 1` case of `sigNeg_le_of_add_sum_sq_nonneg`: one off-line conjugate-pole
contributes at most one negative square. With `CarrierPickKernel.conj_pair_pick_not_posSemidef`
(`κ₋ ≥ 1`) this is the exact `κ₋ = 1` for a single off-line pole — once the complex Pick matrix is
realified into this quadratic-form setting (the remaining Stage-1 wiring). -/
theorem sigNeg_le_one_of_add_sq_nonneg {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (ℓ : M →ₗ[ℝ] ℝ)
    (h : ∀ x, 0 ≤ Q x + (ℓ x) ^ 2) : sigNeg Q ≤ 1 := by
  have := sigNeg_le_of_add_sum_sq_nonneg Q (k := 1) (fun _ => ℓ)
    (fun x => by simpa [Fin.sum_univ_one] using h x)
  simpa using this

/-- **Complex Hermitian Krein–Langer bound, applied directly to the carrier (`κ₋ ≤ k`).** This is the
inertia bound for the *actual* complex Hermitian object — the carrier Pick matrix — with **no
realification** needed. If a Hermitian quadratic form `x ↦ Re(x* H x)` becomes nonnegative after
adding `k` squared moduli of linear functionals `‖⟨v_i, x⟩‖²` (i.e. `H` is positive-semidefinite up
to `k` rank-one terms `v_i v_i*`), then every subspace `W` on which `H` is negative-definite has
`dim_ℂ W ≤ k`. Mechanism (over `ℂ`, mirroring the real `sigNeg_le_of_add_sum_sq_nonneg`): on `W` the
`ℂ`-linear map `x ↦ (⟨v_i, x⟩)_{i<k} ∈ ℂ^k` is injective — if all `⟨v_i, x⟩ = 0` then
`Re(x* H x) ≥ 0`, contradicting negativity — so `W` embeds in `ℂ^k`. This is the carrier statement
"at most `k` off-line poles ⟹ negative inertia `κ₋ ≤ k`" directly on the Hermitian Pick matrix; the
remaining Stage-1 brick is the structural decomposition exhibiting the carrier Pick matrix as
`(PSD) + ∑ (rank-one)` with `k = #{off-line poles}`. -/
theorem hermitian_neg_inertia_le {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin k → (Fin n → ℂ))
    (hbound : ∀ x : Fin n → ℂ, 0 ≤ (star x ⬝ᵥ H.mulVec x).re + ∑ i, ‖star (v i) ⬝ᵥ x‖ ^ 2)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W ≤ k := by
  set G : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun x => star (v i) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ x y
      map_smul' := fun c x => dotProduct_smul c _ x }) with hG
  have hinj : Function.Injective (G.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    by_contra hy0
    have hyval : (y : Fin n → ℂ) ≠ 0 := fun hc => hy0 (Subtype.ext hc)
    have hneg : (star (y : Fin n → ℂ) ⬝ᵥ H.mulVec (y : Fin n → ℂ)).re < 0 := hW _ y.2 hyval
    have hall : ∀ i, star (v i) ⬝ᵥ (y : Fin n → ℂ) = 0 := by
      intro i
      have hi := congrFun hy i
      simpa [hG, LinearMap.domRestrict_apply, LinearMap.pi_apply] using hi
    have hsum : ∑ i, ‖star (v i) ⬝ᵥ (y : Fin n → ℂ)‖ ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hall i]; simp)
    have hb := hbound (y : Fin n → ℂ)
    rw [hsum, add_zero] at hb
    linarith
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun ℂ] at hle

/-- **The factorization ⟹ inertia bound, in PosSemidef language (the carrier-files interface).** If a
Hermitian matrix `H` becomes positive semidefinite after adding `k` rank-one corrections
`v_i v_i*` (i.e. `H + ∑_i v_i v_i* ⪰ 0`, the Krein–Langer factored form), then any subspace `W` on
which `H` is negative-definite has `dim_ℂ W ≤ k`. This is `hermitian_neg_inertia_le` re-expressed
through `Matrix.PosSemidef` — the language of `CarrierPickKernel`/`MeasureCarrier` — via the rank-one
identity `star x ⬝ᵥ (v_i v_i*) x = ‖⟨v_i, x⟩‖²`. So once the carrier Pick matrix is exhibited in the
factored form `(PSD) − ∑ (rank-one)` with `k = #{off-line poles}`, the exact `κ₋ ≤ #{off-line poles}`
follows immediately. The remaining (genuine, deep) Stage-1 content is producing that factorization
(the Blaschke/Krein–Langer rank-one data); this lemma is the clean bridge that consumes it. -/
theorem neg_inertia_le_of_posSemidef {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin k → (Fin n → ℂ))
    (hPSD : (H + ∑ i, Matrix.of (fun j l => v i j * star (v i l))).PosSemidef)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W ≤ k := by
  refine hermitian_neg_inertia_le H v (fun x => ?_) W hW
  have hrank1 : ∀ i : Fin k,
      star x ⬝ᵥ (Matrix.of (fun j l => v i j * star (v i l))).mulVec x
        = ((‖star (v i) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hmv : (Matrix.of (fun j l => v i j * star (v i l))).mulVec x
        = (star (v i) ⬝ᵥ x) • (v i) := by
      funext j
      simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.star_apply, Pi.smul_apply,
                 smul_eq_mul]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hconj : star x ⬝ᵥ v i = star (star (v i) ⬝ᵥ x) := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [hmv, dotProduct_smul, smul_eq_mul, hconj,
        show star (star (v i) ⬝ᵥ x) = (starRingEnd ℂ) (star (v i) ⬝ᵥ x) from rfl,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hP := hPSD.dotProduct_mulVec_nonneg x
  rw [add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum] at hP
  simp_rw [hrank1] at hP
  have hre := (Complex.le_def.mp hP).1
  simp only [Complex.zero_re, Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re] at hre
  exact hre

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **One-point negative-vector witness.** A `1 × 1` complex matrix whose single diagonal entry has
negative real part has an explicit vector on which the Hermitian quadratic expression is negative.
This is the smallest lower-bound primitive for the Krein-Langer inertia ledger: it proves existence
of an actual negative direction, not merely failure of positive semidefiniteness. -/
theorem oneByOne_negative_vector_of_re_neg (c : ℂ) (hc : c.re < 0) :
    ∃ x : Fin 1 → ℂ, x ≠ 0 ∧
      (star x ⬝ᵥ (Matrix.of (fun (_ _ : Fin 1) => c)).mulVec x).re < 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    norm_num at h0
  · simpa [Matrix.mulVec, dotProduct] using hc

/-- Outer product `w w*` is positive semidefinite (`= (col w)(col w)ᴴ`). -/
theorem outer_posSemidef {n : ℕ} (w : Fin n → ℂ) :
    (Matrix.of (fun j l => w j * star (w l))).PosSemidef := by
  have h : (Matrix.of (fun j l => w j * star (w l)))
      = (Matrix.of (fun (j : Fin n) (_ : Fin 1) => w j)) *
          (Matrix.of (fun (j : Fin n) (_ : Fin 1) => w j))ᴴ := by
    ext j l; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]; exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The per-entry conjugate-pair Pick identity, as a formal rational identity in four atoms:
`(m(z_j) - conj m(z_k))/(z_j - conj z_k) = a_j conj(e_k) + e_j conj(a_k)` with `a=1/(t-·)`,
`e=1/(t̄-·)`. The Cauchy-telescoping `(q-p)/(pq) = 1/p - 1/q` applied at both poles. -/
theorem conjPair_pe (t cT zj czk : ℂ)
    (h1 : t - zj ≠ 0) (h2 : cT - zj ≠ 0) (h3 : t - czk ≠ 0) (h4 : cT - czk ≠ 0) (hD : zj - czk ≠ 0) :
    (((t - zj)⁻¹ + (cT - zj)⁻¹) - ((cT - czk)⁻¹ + (t - czk)⁻¹)) / (zj - czk)
      = (t - zj)⁻¹ * (t - czk)⁻¹ + (cT - zj)⁻¹ * (cT - czk)⁻¹ := by
  rw [div_eq_iff hD]; field_simp; ring

/-- The FE-symmetric conjugate-pair carrier `m(z) = 1/(t-z) + 1/(t̄-z)` (real on `ℝ`; one off-line
zero pair `{t, t̄}`). -/
noncomputable def conjPairCarrier (t z : ℂ) : ℂ := (t - z)⁻¹ + (star t - z)⁻¹

/-- The finite Pick matrix of the conjugate-pair carrier on nodes `z`. -/
noncomputable def conjPairPick {N : ℕ} (t : ℂ) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun j k => (conjPairCarrier t (z j) - star (conjPairCarrier t (z k))) / (z j - star (z k)))

/-- **Exact `κ₋ = 1` for one off-line zero (the explicit Krein–Langer factorization).** For the
FE-symmetric conjugate-pair carrier `m(z)=1/(t-z)+1/(t̄-z)` with `t, z_j ∈ ℂ⁺` and no node at the pole
(`z_j ≠ t`), the Pick matrix has negative inertia `≤ 1`: any subspace on which the Pick form is
negative-definite has `dim_ℂ ≤ 1`. The witness is the explicit rank-one factorization (with
`a_j = 1/(t-z_j)`, `e_j = 1/(t̄-z_j)`):
`2 · Pick = (e+a)(e+a)* − (e−a)(e−a)*`, hence `2·Pick + (e−a)(e−a)* = (e+a)(e+a)* ⪰ 0` —
one rank-one correction suffices, so `κ₋ ≤ 1` by `neg_inertia_le_of_posSemidef`. Combined with the
lower bound `CarrierPickKernel.conj_pair_pick_not_posSemidef` (`κ₋ ≥ 1`) this pins the **exact
`κ₋ = 1`**: one off-line zero contributes exactly one negative square. This closes the Stage-1
exact-inertia core for a single off-line zero — the deep Blaschke/Krein–Langer content, here computed
in closed form (numerically pre-certified to machine precision before formalization). -/
theorem conj_pair_pick_neg_inertia_le_one {N : ℕ} (t : ℂ) (z : Fin N → ℂ)
    (ht : 0 < t.im) (hz : ∀ j, 0 < (z j).im) (hjt : ∀ j, z j ≠ t)
    (W : Submodule ℂ (Fin N → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ (conjPairPick t z).mulVec x).re < 0) :
    Module.finrank ℂ W ≤ 1 := by
  set a : Fin N → ℂ := fun j => (t - z j)⁻¹ with ha
  set e : Fin N → ℂ := fun j => (star t - z j)⁻¹ with he
  have hne : ∀ (u v : ℂ), u.im ≠ v.im → u - v ≠ 0 := by
    intro u v h hc; apply h
    have h2 : (u - v).im = 0 := by rw [hc]; rfl
    rw [Complex.sub_im, sub_eq_zero] at h2; exact h2
  have ht1 : ∀ j, t - z j ≠ 0 := fun j => sub_ne_zero.mpr (fun hc => hjt j hc.symm)
  have ht2 : ∀ j, star t - z j ≠ 0 := fun j =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j])
  have ht3 : ∀ k, t - star (z k) ≠ 0 := fun k =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz k])
  have ht4 : ∀ k, star t - star (z k) ≠ 0 := fun k => by
    rw [← star_sub]; exact star_ne_zero.mpr (ht1 k)
  have hDk : ∀ j k, z j - star (z k) ≠ 0 := fun j k =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, hz k])
  have hPe : ∀ j k, conjPairPick t z j k = a j * star (e k) + e j * star (a k) := by
    intro j k
    simp only [conjPairPick, Matrix.of_apply, conjPairCarrier, ha, he,
               star_add, star_inv₀, star_sub, star_star]
    exact conjPair_pe t (star t) (z j) (star (z k)) (ht1 j) (ht2 j) (ht3 k) (ht4 k) (hDk j k)
  refine neg_inertia_le_of_posSemidef ((2 : ℂ) • conjPairPick t z)
    (fun _ => fun j => e j - a j) ?_ W ?_
  · have hid : (2 : ℂ) • conjPairPick t z
        + ∑ _i : Fin 1, Matrix.of (fun j l => (e j - a j) * star (e l - a l))
        = Matrix.of (fun j l => (e j + a j) * star (e l + a l)) := by
      ext j k
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
                 Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, smul_eq_mul,
                 star_sub, star_add]
      rw [hPe j k]; ring
    rw [hid]; exact outer_posSemidef _
  · intro x hx hx0
    have hWx := hW x hx hx0
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul,
        show ((2 : ℂ) * (star x ⬝ᵥ (conjPairPick t z).mulVec x)).re
          = 2 * (star x ⬝ᵥ (conjPairPick t z).mulVec x).re from by simp [Complex.mul_re]]
    linarith

/-- The carrier with `k` off-line zero pairs: `m(z) = ∑_{i<k} [1/(t_i-z) + 1/(t̄_i-z)]`. -/
noncomputable def multiPairCarrier {k : ℕ} (t : Fin k → ℂ) (z : ℂ) : ℂ :=
  ∑ i, ((t i - z)⁻¹ + (star (t i) - z)⁻¹)

/-- Its finite Pick matrix on nodes `z`. -/
noncomputable def multiPairPick {N k : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun j l => (multiPairCarrier t (z j) - star (multiPairCarrier t (z l))) / (z j - star (z l)))

/-- **General Krein–Langer bound `κ₋ ≤ k` for `k` off-line zeros.** For the FE-symmetric carrier with
`k` conjugate pairs `m(z)=∑_{i<k}[1/(t_i-z)+1/(t̄_i-z)]` (each `t_i ∈ ℂ⁺`, nodes `z_j ∈ ℂ⁺`, no node at
a pole), the Pick matrix has negative inertia `≤ k`: any subspace on which the Pick form is
negative-definite has `dim_ℂ ≤ k`. Since the Pick kernel is additive in the carrier, the per-pole
factorizations sum: `2·Pick = ∑_i [(e_i+a_i)(e_i+a_i)* − (e_i−a_i)(e_i−a_i)*]`
(`a_i = 1/(t_i-·)`, `e_i = 1/(t̄_i-·)`), so `2·Pick + ∑_i (e_i−a_i)(e_i−a_i)* = ∑_i (e_i+a_i)(e_i+a_i)*`
— a sum of `k` outer products (PSD), i.e. `k` rank-one corrections suffice. Generalizes
`conj_pair_pick_neg_inertia_le_one` (`k=1`). The matching lower bound (`κ₋ ≥ k`, a multi-node Pick
witness) would pin the exact `κ₋ = k`: each off-line zero contributes exactly one negative square. -/
theorem multi_pair_pick_neg_inertia_le {N k : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ)
    (ht : ∀ i, 0 < (t i).im) (hz : ∀ j, 0 < (z j).im) (hjt : ∀ i j, z j ≠ t i)
    (W : Submodule ℂ (Fin N → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ (multiPairPick t z).mulVec x).re < 0) :
    Module.finrank ℂ W ≤ k := by
  set a : Fin k → Fin N → ℂ := fun i j => (t i - z j)⁻¹ with ha
  set e : Fin k → Fin N → ℂ := fun i j => (star (t i) - z j)⁻¹ with he
  have hne : ∀ (u v : ℂ), u.im ≠ v.im → u - v ≠ 0 := by
    intro u v h hc; apply h
    have h2 : (u - v).im = 0 := by rw [hc]; rfl
    rw [Complex.sub_im, sub_eq_zero] at h2; exact h2
  have ht1 : ∀ i j, t i - z j ≠ 0 := fun i j => sub_ne_zero.mpr (fun hc => hjt i j hc.symm)
  have ht2 : ∀ i j, star (t i) - z j ≠ 0 := fun i j =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, ht i])
  have ht3 : ∀ i l, t i - star (z l) ≠ 0 := fun i l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz l, ht i])
  have ht4 : ∀ i l, star (t i) - star (z l) ≠ 0 := fun i l => by
    rw [← star_sub]; exact star_ne_zero.mpr (ht1 i l)
  have hDk : ∀ j l, z j - star (z l) ≠ 0 := fun j l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, hz l])
  have hPe : ∀ j l, multiPairPick t z j l = ∑ i, (a i j * star (e i l) + e i j * star (a i l)) := by
    intro j l
    rw [multiPairPick, Matrix.of_apply, multiPairCarrier, multiPairCarrier, star_sum,
        ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha, he, star_add, star_inv₀, star_sub, star_star]
    exact conjPair_pe (t i) (star (t i)) (z j) (star (z l)) (ht1 i j) (ht2 i j) (ht3 i l) (ht4 i l) (hDk j l)
  refine neg_inertia_le_of_posSemidef ((2 : ℂ) • multiPairPick t z)
    (fun i => fun j => e i j - a i j) ?_ W ?_
  · have hid : (2 : ℂ) • multiPairPick t z
        + ∑ i, Matrix.of (fun j l => (e i j - a i j) * star (e i l - a i l))
        = ∑ i, Matrix.of (fun j l => (e i j + a i j) * star (e i l + a i l)) := by
      ext j l
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
                 smul_eq_mul, star_sub, star_add]
      rw [hPe j l, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hid]
    exact Matrix.posSemidef_sum Finset.univ (fun i _ => outer_posSemidef _)
  · intro x hx hx0
    have hWx := hW x hx hx0
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul,
        show ((2 : ℂ) * (star x ⬝ᵥ (multiPairPick t z).mulVec x)).re
          = 2 * (star x ⬝ᵥ (multiPairPick t z).mulVec x).re from by simp [Complex.mul_re]]
    linarith

/-- **Companion positive-inertia bound `κ₊ ≤ k`.** For the same `k`-pair carrier, any subspace on
which the Pick form is *positive*-definite also has `dim_ℂ ≤ k`: apply the inertia bound to `H = −2·Pick`
with the dual factorization `−2·Pick + ∑_i (e_i+a_i)(e_i+a_i)* = ∑_i (e_i−a_i)(e_i−a_i)* ⪰ 0`. With
`multi_pair_pick_neg_inertia_le` (`κ₋ ≤ k`) this shows the `k`-pair Pick matrix has **rank ≤ 2k** —
both inertias are bounded by the number of off-line zeros. The exact `κ₋ = k` additionally needs the
matching lower bound (Cauchy-rank non-degeneracy of the `2k` pole-vectors `{a_i, e_i}`). -/
theorem multi_pair_pick_pos_inertia_le {N k : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ)
    (ht : ∀ i, 0 < (t i).im) (hz : ∀ j, 0 < (z j).im) (hjt : ∀ i j, z j ≠ t i)
    (W : Submodule ℂ (Fin N → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (multiPairPick t z).mulVec x).re) :
    Module.finrank ℂ W ≤ k := by
  set a : Fin k → Fin N → ℂ := fun i j => (t i - z j)⁻¹ with ha
  set e : Fin k → Fin N → ℂ := fun i j => (star (t i) - z j)⁻¹ with he
  have hne : ∀ (u v : ℂ), u.im ≠ v.im → u - v ≠ 0 := by
    intro u v h hc; apply h
    have h2 : (u - v).im = 0 := by rw [hc]; rfl
    rw [Complex.sub_im, sub_eq_zero] at h2; exact h2
  have ht1 : ∀ i j, t i - z j ≠ 0 := fun i j => sub_ne_zero.mpr (fun hc => hjt i j hc.symm)
  have ht2 : ∀ i j, star (t i) - z j ≠ 0 := fun i j =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, ht i])
  have ht3 : ∀ i l, t i - star (z l) ≠ 0 := fun i l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz l, ht i])
  have ht4 : ∀ i l, star (t i) - star (z l) ≠ 0 := fun i l => by
    rw [← star_sub]; exact star_ne_zero.mpr (ht1 i l)
  have hDk : ∀ j l, z j - star (z l) ≠ 0 := fun j l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, hz l])
  have hPe : ∀ j l, multiPairPick t z j l = ∑ i, (a i j * star (e i l) + e i j * star (a i l)) := by
    intro j l
    rw [multiPairPick, Matrix.of_apply, multiPairCarrier, multiPairCarrier, star_sum,
        ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha, he, star_add, star_inv₀, star_sub, star_star]
    exact conjPair_pe (t i) (star (t i)) (z j) (star (z l)) (ht1 i j) (ht2 i j) (ht3 i l) (ht4 i l) (hDk j l)
  refine neg_inertia_le_of_posSemidef ((-2 : ℂ) • multiPairPick t z)
    (fun i => fun j => e i j + a i j) ?_ W ?_
  · have hid : (-2 : ℂ) • multiPairPick t z
        + ∑ i, Matrix.of (fun j l => (e i j + a i j) * star (e i l + a i l))
        = ∑ i, Matrix.of (fun j l => (e i j - a i j) * star (e i l - a i l)) := by
      ext j l
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
                 smul_eq_mul, star_sub, star_add]
      rw [hPe j l, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hid]
    exact Matrix.posSemidef_sum Finset.univ (fun i _ => outer_posSemidef _)
  · intro x hx hx0
    have hWx := hW x hx hx0
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul,
        show ((-2 : ℂ) * (star x ⬝ᵥ (multiPairPick t z).mulVec x)).re
          = -2 * (star x ⬝ᵥ (multiPairPick t z).mulVec x).re from by simp [Complex.mul_re]]
    linarith

/-- **The explicit Krein–Langer factorization as a matrix identity** (`2·Pick = (e+a)(e+a)* − (e−a)(e−a)*`).
The conjugate-pair Pick matrix is the difference of two rank-one positive matrices, with
`a_j = 1/(t-z_j)`, `e_j = 1/(t̄-z_j)`. This is the central computational lever: the upper bound `κ₋ ≤ 1`
adds back `(e−a)(e−a)*` to reach the PSD `(e+a)(e+a)*`; the lower bound `κ₋ ≥ 1` evaluates the form on
a vector orthogonal to `e+a` (where it is `−‖⟨e−a,·⟩‖² < 0`). Numerically pre-certified to machine
precision (`computations/krein_langer_single_pole/`). -/
theorem conj_pair_pick_factorization {N : ℕ} (t : ℂ) (z : Fin N → ℂ)
    (ht : 0 < t.im) (hz : ∀ j, 0 < (z j).im) (hjt : ∀ j, z j ≠ t) :
    (2 : ℂ) • conjPairPick t z
      = Matrix.of (fun j l => ((star t - z j)⁻¹ + (t - z j)⁻¹) * star ((star t - z l)⁻¹ + (t - z l)⁻¹))
        - Matrix.of (fun j l => ((star t - z j)⁻¹ - (t - z j)⁻¹) * star ((star t - z l)⁻¹ - (t - z l)⁻¹)) := by
  have hne : ∀ (u v : ℂ), u.im ≠ v.im → u - v ≠ 0 := by
    intro u v h hc; apply h
    have h2 : (u - v).im = 0 := by rw [hc]; rfl
    rw [Complex.sub_im, sub_eq_zero] at h2; exact h2
  have ht1 : ∀ j, t - z j ≠ 0 := fun j => sub_ne_zero.mpr (fun hc => hjt j hc.symm)
  have ht2 : ∀ j, star t - z j ≠ 0 := fun j =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j])
  have ht3 : ∀ l, t - star (z l) ≠ 0 := fun l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz l])
  have ht4 : ∀ l, star t - star (z l) ≠ 0 := fun l => by
    rw [← star_sub]; exact star_ne_zero.mpr (ht1 l)
  have hDk : ∀ j l, z j - star (z l) ≠ 0 := fun j l =>
    hne _ _ (by simp only [Complex.star_def, Complex.conj_im]; linarith [hz j, hz l])
  have hPe : ∀ j l, conjPairPick t z j l
      = (t - z j)⁻¹ * star ((star t - z l)⁻¹) + (star t - z j)⁻¹ * star ((t - z l)⁻¹) := by
    intro j l
    simp only [conjPairPick, Matrix.of_apply, conjPairCarrier, star_add, star_inv₀, star_sub, star_star]
    exact conjPair_pe t (star t) (z j) (star (z l)) (ht1 j) (ht2 j) (ht3 l) (ht4 l) (hDk j l)
  ext j l
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, star_sub, star_add]
  rw [hPe j l]; ring

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **One-point negative subspace witness.** A `1 × 1` complex matrix whose single entry has
negative real part is negative-definite on the whole one-dimensional ambient space. This upgrades the
one-point lower witness from an explicit vector to an explicit negative subspace of complex dimension
one, matching the subspace language consumed by `hermitian_neg_inertia_le`. -/
theorem oneByOne_negative_subspace_of_re_neg (c : ℂ) (hc : c.re < 0) :
    Module.finrank ℂ (⊤ : Submodule ℂ (Fin 1 → ℂ)) = 1 ∧
      ∀ x ∈ (⊤ : Submodule ℂ (Fin 1 → ℂ)), x ≠ 0 →
        (star x ⬝ᵥ (Matrix.of (fun (_ _ : Fin 1) => c)).mulVec x).re < 0 := by
  constructor
  · simp
  · intro x _ hx
    have hx0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      funext i
      fin_cases i
      exact h0
    have hnorm : 0 < ‖x 0‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx0)
    have hquad :
        (star x ⬝ᵥ (Matrix.of (fun (_ _ : Fin 1) => c)).mulVec x).re =
          c.re * ‖x 0‖ ^ 2 := by
      simp [Matrix.mulVec, dotProduct]
      rw [← Complex.normSq_eq_norm_sq (x 0), Complex.normSq_apply]
      ring
    nlinarith

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **Diagonal lower-bound witness (`κ₋ ≥ k` for an already isolated diagonal block).** If the
entries of a diagonal complex matrix all have strictly negative real part, then the whole ambient
`k`-dimensional space is a negative subspace for the Hermitian quadratic expression. This is the
finite linear-algebra primitive needed by the Stage-1 lower-bound program after the multi-pair Pick
kernel has been reduced to, or isolated on, a diagonal negative block: it turns `k` independent
one-point negative tests into a genuine `k`-dimensional negative subspace. -/
theorem diagonal_negative_subspace {k : ℕ} (c : Fin k → ℂ) (hc : ∀ i, (c i).re < 0) :
    Module.finrank ℂ (⊤ : Submodule ℂ (Fin k → ℂ)) = k ∧
      ∀ x ∈ (⊤ : Submodule ℂ (Fin k → ℂ)), x ≠ 0 →
        (star x ⬝ᵥ (Matrix.diagonal c).mulVec x).re < 0 := by
  constructor
  · simp
  · intro x _ hx
    have hnonempty : ∃ i, x i ≠ 0 := by
      by_contra hnone
      apply hx
      funext i
      exact not_not.mp ((not_exists.mp hnone) i)
    have hquad :
        (star x ⬝ᵥ (Matrix.diagonal c).mulVec x).re =
          ∑ i, (c i).re * ‖x i‖ ^ 2 := by
      have hmv : (Matrix.diagonal c).mulVec x = fun i => c i * x i := by
        funext i
        simp [Matrix.mulVec]
      have hterm : ∀ i, (star (x i) * (c i * x i)).re = (c i).re * ‖x i‖ ^ 2 := by
        intro i
        rw [← Complex.normSq_eq_norm_sq (x i), Complex.normSq_apply]
        simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      rw [dotProduct, hmv, Complex.re_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hquad]
    have hle : ∀ i, (c i).re * ‖x i‖ ^ 2 ≤ 0 := by
      intro i
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hc i)) (sq_nonneg _)
    obtain ⟨i0, hi0x⟩ := hnonempty
    have hi0 : (c i0).re * ‖x i0‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (hc i0) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi0x))
    have herase : ∑ i ∈ Finset.univ.erase i0, (c i).re * ‖x i‖ ^ 2 ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hle i)
    have hdecomp : ∑ i, (c i).re * ‖x i‖ ^ 2 =
        (∑ i ∈ Finset.univ.erase i0, (c i).re * ‖x i‖ ^ 2) + (c i0).re * ‖x i0‖ ^ 2 := by
      rw [← Finset.sum_erase_add Finset.univ (fun i => (c i).re * ‖x i‖ ^ 2)
        (Finset.mem_univ i0)]
    rw [hdecomp]
    linarith

/-- Rank-one quadratic identity: `x* (v v*) x = ‖⟨v,x⟩‖²`. -/
theorem rankOne_quadForm {n : ℕ} (v x : Fin n → ℂ) :
    star x ⬝ᵥ (Matrix.of (fun p q => v p * star (v q))).mulVec x = ((‖star v ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
  have hmv : (Matrix.of (fun p q => v p * star (v q))).mulVec x = (star v ⬝ᵥ x) • v := by
    funext p
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun l _ => by ring)
  have hconj : star x ⬝ᵥ v = star (star v ⬝ᵥ x) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hmv, dotProduct_smul, smul_eq_mul, hconj,
      show star (star v ⬝ᵥ x) = (starRingEnd ℂ) (star v ⬝ᵥ x) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The lower-bound bridge (dual of `neg_inertia_le_of_posSemidef`).** For the factored Hermitian
matrix `H = ∑_i w_i w_i* − ∑_i u_i u_i*`, a vector `x` orthogonal to every `w_i` at which the `u_i` do
not all vanish is a **negative direction**: `x*Hx = ∑|⟨w_i,x⟩|² − ∑|⟨u_i,x⟩|² = 0 − (>0) < 0`. Applied
to a `k`-dimensional subspace `W` orthogonal to all `w_i` with the `u_i` jointly nonvanishing on
`W∖{0}`, this exhibits a `k`-dim negative-definite subspace, i.e. `κ₋ ≥ k` — the matching lower bound
to `neg_inertia_le_of_posSemidef`. For the carrier (`w_i=e_i+a_i`, `u_i=e_i−a_i`) the only remaining
input is constructing that `W` (Cauchy non-degeneracy of `{a_i, e_i}`), per the roadmap strategy. -/
theorem neg_def_of_factored_orthogonal {N k : ℕ} (w u : Fin k → (Fin N → ℂ))
    (x : Fin N → ℂ) (hw : ∀ i, star (w i) ⬝ᵥ x = 0) (hu : ∃ i, star (u i) ⬝ᵥ x ≠ 0) :
    (star x ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
       - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec x).re < 0 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, Matrix.sum_mulVec,
      dotProduct_sum, dotProduct_sum]
  simp_rw [rankOne_quadForm]
  rw [show (∑ i, ((‖star (w i) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ)) = 0 from
        Finset.sum_eq_zero (fun i _ => by rw [hw i]; simp)]
  rw [zero_sub, ← Complex.ofReal_sum]
  obtain ⟨i0, hi0⟩ := hu
  have hpos : 0 < ∑ i, ‖star (u i) ⬝ᵥ x‖ ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, by positivity⟩
  simp only [Complex.neg_re, Complex.ofReal_re]
  linarith

/-- **The exact lower-bound construction (`κ₋ ≥ k`).** If the evaluation map
`(Φ,Ψ): x ↦ (⟨w_i,x⟩_i, ⟨u_i,x⟩_i) : ℂ^N → ℂ^k × ℂ^k` is surjective (the Cauchy non-degeneracy of the
`2k` vectors `{w_i, u_i}`), then for `H = ∑_i w_i w_i* − ∑_i u_i u_i*` there is a `k`-dimensional
subspace on which `H` is negative-definite. Construction: take preimages `x_m` of `(0, δ_m)` (so
`Φ(x_m)=0`, `Ψ(x_m)=δ_m`); the section `S = ∑_m c_m • x_m` satisfies `Ψ∘S = id` (hence `S` injective,
`dim range S = k`) and `Φ∘S = 0` (so `range S ⊥ {w_i}`); on `range S`, `Ψ y = c ≠ 0` for `y≠0`, so
some `⟨u_i,y⟩ ≠ 0`, and `neg_def_of_factored_orthogonal` gives negativity. -/
theorem exists_neg_def_subspace {N k : ℕ} (w u : Fin k → (Fin N → ℂ))
    (Φ Ψ : (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin N → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin N → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) :
    ∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = k ∧
      ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
         - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0 := by
  choose x hx using fun m => hT (0, Pi.single m 1)
  have hΦx : ∀ m, Φ (x m) = 0 := fun m => (Prod.mk.injEq _ _ _ _).mp (hx m) |>.1
  have hΨx : ∀ m, Ψ (x m) = Pi.single m 1 := fun m => (Prod.mk.injEq _ _ _ _).mp (hx m) |>.2
  set S : (Fin k → ℂ) →ₗ[ℂ] (Fin N → ℂ) := Fintype.linearCombination ℂ x with hS
  have hΨS : Ψ.comp S = LinearMap.id := by
    apply LinearMap.ext; intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hS, Fintype.linearCombination_apply,
               map_sum, map_smul, hΨx]
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  have hΦS : Φ.comp S = 0 := by
    apply LinearMap.ext; intro c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hS, Fintype.linearCombination_apply,
               map_sum, map_smul, hΦx, smul_zero, Finset.sum_const_zero]
  have hSinj : Function.Injective S := LinearMap.injective_of_comp_eq_id S Ψ hΨS
  refine ⟨LinearMap.range S, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hSinj, Module.finrank_fin_fun]
  · intro y hy hy0
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
    have hΦy : ∀ i, star (w i) ⬝ᵥ (S c) = 0 := by
      intro i
      have : Φ (S c) = 0 := by rw [← LinearMap.comp_apply, hΦS, LinearMap.zero_apply]
      rw [← hΦ]; rw [this]; rfl
    have hcne : c ≠ 0 := fun hc => hy0 (by rw [hc, map_zero])
    have hΨy : ∃ i, star (u i) ⬝ᵥ (S c) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hcne
      refine ⟨i, ?_⟩
      have : Ψ (S c) = c := by rw [← LinearMap.comp_apply, hΨS, LinearMap.id_apply]
      rw [← hΨ, this]; simpa using hi
    exact neg_def_of_factored_orthogonal w u (S c) hΦy hΨy

/-- **Exact Krein–Langer inertia `κ₋ = k`** for the factored Hermitian matrix
`H = ∑_i w_i w_i* − ∑_i u_i u_i*`, given the evaluation map `(Φ,Ψ): x ↦ (⟨w_i,x⟩, ⟨u_i,x⟩)` surjective
(Cauchy non-degeneracy of `{w_i, u_i}`): the negative inertia is **exactly `k`** — every
negative-definite subspace has `dim ≤ k` (upper, via `H + ∑ u_i u_i* = ∑ w_i w_i* ⪰ 0`), and one of
`dim = k` exists (lower, `exists_neg_def_subspace`). For the conjugate-pair carrier
(`w_i=e_i+a_i`, `u_i=e_i−a_i`) the surjectivity hypothesis is exactly the Cauchy independence of the
`2k` pole-vectors `{a_i, e_i}` — the sole remaining arithmetic input for the closed-form `κ₋ = #off-line zeros`. -/
theorem exact_neg_inertia {N k : ℕ} (w u : Fin k → (Fin N → ℂ))
    (Φ Ψ : (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin N → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin N → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) :
    (∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0) := by
  refine ⟨fun W hWneg => ?_, exists_neg_def_subspace w u Φ Ψ hΦ hΨ hT⟩
  refine neg_inertia_le_of_posSemidef _ u ?_ W hWneg
  rw [sub_add_cancel]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => outer_posSemidef _)

open Polynomial in
/-- **Cauchy matrices are nonsingular: the Cauchy vectors are linearly independent.** For distinct
poles `p` and distinct nodes `z` (with `p_i ≠ z_j`), the family of Cauchy vectors
`v_i = (j ↦ (p_i - z_j)⁻¹)` is linearly independent. Proof: a dependence `∑_i c_i (p_i-z_j)⁻¹ = 0`
clears to a polynomial `Q(X) = ∑_i c_i ∏_{l≠i}(p_l - X)` of degree `< n` vanishing at the `n` distinct
nodes, so `Q = 0`; evaluating at `p_m` gives `c_m ∏_{l≠m}(p_l-p_m) = 0`, hence `c_m = 0`. This is the
arithmetic core of the exact Krein–Langer count: applied to the `2k` poles `{t_i, t̄_i}` it gives the
Cauchy non-degeneracy of `{a_i, e_i}` underlying the surjectivity hypothesis of `exact_neg_inertia`. -/
theorem cauchy_linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] (p z : ι → ℂ)
    (hp : Function.Injective p) (hz : Function.Injective z) (hpz : ∀ i j, p i ≠ z j) :
    LinearIndependent ℂ (fun i => (fun j => (p i - z j)⁻¹ : ι → ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have hcj : ∀ j, ∑ i, c i * (p i - z j)⁻¹ = 0 := by
    intro j
    have h := congrFun hc j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  set Q : ℂ[X] := ∑ i, C (c i) * ∏ l ∈ Finset.univ.erase i, (C (p l) - X) with hQ
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨m⟩
  have hdeg : Q.natDegree < Fintype.card ι := by
    have hle : Q.natDegree ≤ Fintype.card ι - 1 := by
      rw [hQ]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
      refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
      refine (Finset.sum_le_sum (g := fun _ => 1)
        (fun l _ => (natDegree_sub_le _ _).trans (by simp))).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  have hev : ∀ j, Q.eval (z j) = 0 := by
    intro j
    rw [hQ]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    have key : (∏ l, (p l - z j)) * (∑ i, c i * (p i - z j)⁻¹)
        = ∑ i, c i * ∏ l ∈ Finset.univ.erase i, (p l - z j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      have hi : p i - z j ≠ 0 := sub_ne_zero.mpr (hpz i j)
      field_simp
    rw [hcj j, mul_zero] at key
    exact key.symm
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hz hev hdeg
  have hevpm : Q.eval (p m) = c m * ∏ l ∈ Finset.univ.erase m, (p l - p m) := by
    rw [hQ]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.sum_eq_single m]
    · intro i _ hi
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ m⟩)
            (by ring)]
      ring
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hQ0, eval_zero] at hevpm
  have hprodne : ∏ l ∈ Finset.univ.erase m, (p l - p m) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    exact sub_ne_zero.mpr (fun heq => (Finset.mem_erase.mp hl).1 (hp heq))
  exact (mul_eq_zero.mp hevpm.symm).resolve_right hprodne

/-- **Independence ⟹ evaluation surjective (the connecting layer).** For a linearly independent
family `v : m → (m → ℂ)` (square index `m`), the evaluation map `x ↦ (⟨v_i, x⟩)_i` is surjective.
Proof: the matrix `M` with columns `v_i` is a unit (`linearIndependent_cols_iff_isUnit`), so `Mᴴ` is a
unit and `Mᴴ.mulVec` (= the evaluation map) is surjective. This is the layer joining
`cauchy_linearIndependent` (the `2k` Cauchy vectors `{a_i, e_i}` are independent) to the surjectivity
hypothesis of `exact_neg_inertia`: together they make the exact `κ₋ = k` unconditional for the
conjugate-pair carrier on `2k` nodes (combining `w_i, u_i` over the index `Fin k ⊕ Fin k`). -/
theorem eval_surjective_of_linearIndependent {m : Type*} [Fintype m] [DecidableEq m]
    (v : m → (m → ℂ)) (hv : LinearIndependent ℂ v) :
    Function.Surjective (fun x : m → ℂ => (fun i => star (v i) ⬝ᵥ x : m → ℂ)) := by
  set M : Matrix m m ℂ := Matrix.of (fun j i => v i j) with hM
  have hcol : M.col = v := by funext i j; simp [Matrix.col_apply, hM]
  have hunit : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]; exact hv
  have hsurj : Function.Surjective (Mᴴ).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_conjTranspose M).mpr hunit)
  have hE : (fun x : m → ℂ => (fun i => star (v i) ⬝ᵥ x : m → ℂ)) = Mᴴ.mulVec := by
    funext x i
    simp only [Matrix.mulVec, Matrix.conjTranspose_apply, hM, Matrix.of_apply, dotProduct,
               Pi.star_apply]
  rw [hE]; exact hsurj
/-- **Independence ⟹ evaluation surjective (rectangular, via the Gram matrix).** For any linearly
independent family `V : ι → (Fin N → ℂ)` (`ι` a fintype, `card ι ≤ N`), the evaluation map
`x ↦ (⟨V_j, x⟩)_j : (Fin N → ℂ) → (ι → ℂ)` is surjective. Proof: with `M` the matrix of columns `V_j`,
`M.mulVec` is injective (independence), so the Gram matrix `Mᴴ M` is positive-definite
(`PosDef.conjTranspose_mul_self`), hence a unit; its `mulVec` is surjective, and it factors as
`evaluation ∘ (c ↦ ∑ c_j V_j)`, forcing the evaluation surjective. Unlike the square
`eval_surjective_of_linearIndependent`, this applies over the carrier's actual node space `Fin N`
(`N ≥ card ι`), with `ι = Fin k ⊕ Fin k` the combined off-line-pole index — the connecting layer that
makes `exact_neg_inertia` unconditional once `{a_i, e_i}` are shown Cauchy-independent. -/
theorem eval_surjective_rect {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → (Fin N → ℂ)) (hv : LinearIndependent ℂ V) :
    Function.Surjective (fun x : Fin N → ℂ => (fun j => star (V j) ⬝ᵥ x : ι → ℂ)) := by
  set M : Matrix (Fin N) ι ℂ := Matrix.of (fun i j => V j i) with hM
  have hmulvec : ∀ c, M.mulVec c = ∑ j, c j • V j := by
    intro c; funext i
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
               smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hinj : Function.Injective M.mulVec := by
    intro c1 c2 h12
    have hsub : M.mulVec (c1 - c2) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    rw [hmulvec] at hsub
    funext j
    have := (Fintype.linearIndependent_iff.mp hv) (c1 - c2) hsub j
    simpa [sub_eq_zero] using this
  have hGunit : IsUnit (Mᴴ * M) := (Matrix.PosDef.conjTranspose_mul_self M hinj).isUnit
  have hGsurj : Function.Surjective (Mᴴ * M).mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hGunit
  intro b
  obtain ⟨c, hc⟩ := hGsurj b
  refine ⟨M.mulVec c, ?_⟩
  funext j
  show star (V j) ⬝ᵥ M.mulVec c = b j
  rw [← hc, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, Matrix.conjTranspose_apply, hM, Matrix.of_apply, dotProduct, Pi.star_apply]
end

end GaloisForLFunctions
