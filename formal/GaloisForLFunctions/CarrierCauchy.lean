import Mathlib
import GaloisForLFunctions.KreinLangerInertia

/-!
# The conjugate-pair carrier vectors are linearly independent

`formalization-roadmap-finite-to-apex.md` Stage 1 assembly step, building on
`KreinLangerInertia.cauchy_linearIndependent`. That lemma proves the `2k` Cauchy vectors
`{aᵢ, eᵢ}` (with `aᵢ(j) = 1/(tᵢ − zⱼ)`, `eᵢ(j) = 1/(t̄ᵢ − zⱼ)`) are linearly independent for distinct
poles and nodes. The exact Krein–Langer inertia `exact_neg_inertia` is, however, factored through the
carrier vectors `wᵢ = eᵢ + aᵢ`, `uᵢ = eᵢ − aᵢ`, not `{aᵢ, eᵢ}` directly.

This file supplies the missing link: the carrier family `{wᵢ, uᵢ}`, indexed by `Fin k ⊕ Fin k`, is
**linearly independent** (`multiPair_carrier_linearIndependent`). The change of basis
`{eᵢ, aᵢ} → {eᵢ ± aᵢ}` is the per-pair `[[1,1],[1,−1]]` (determinant `−2`), so independence transfers:
a dependence `∑ αᵢ wᵢ + βᵢ uᵢ = 0` rewrites to `∑ (αᵢ+βᵢ) eᵢ + (αᵢ−βᵢ) aᵢ = 0`, forcing
`αᵢ+βᵢ = αᵢ−βᵢ = 0`, hence `αᵢ = βᵢ = 0`. Numerically pre-certified in
`computations/carrier_cauchy_nondegeneracy/` (the stacked `{wᵢ,uᵢ}` determinant is `2ᵏ·det(Cauchy) ≠ 0`
for on-line and off-line nodes).

This is the linear-independence half of the Cauchy non-degeneracy input to `exact_neg_inertia`. What is
**not** here: turning this into the literal `hT : Surjective (Φ.prod Ψ)` of `exact_neg_inertia` (the
`ℂ^k × ℂ^k ≃ ℂ^{k⊕k}` reindexing of the surjective evaluation map), nor the unconditional `κ₋ = k`.
No infinite carrier `m_ξ`, no RH.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions

noncomputable section

/-- **The conjugate-pair carrier vectors are linearly independent.** For `k` distinct off-line poles
`t : Fin k → ℂ` (each `Im tᵢ > 0`) and `2k` distinct nodes `z : Fin (k+k) → ℂ` avoiding the poles and
their conjugates, the carrier family over `Fin k ⊕ Fin k`
`Sum.elim (i ↦ j ↦ (t̄ᵢ−zⱼ)⁻¹ + (tᵢ−zⱼ)⁻¹) (i ↦ j ↦ (t̄ᵢ−zⱼ)⁻¹ − (tᵢ−zⱼ)⁻¹)` — i.e. `{wᵢ = eᵢ+aᵢ}`
on the left summand and `{uᵢ = eᵢ−aᵢ}` on the right — is linearly independent over `ℂ`. Proof: the
underlying Cauchy family `{eᵢ, aᵢ}` (poles `t̄ᵢ` and `tᵢ`, all `2k` distinct since `Im t̄ᵢ < 0 < Im tⱼ`)
is independent by `cauchy_linearIndependent`; the invertible per-pair change of basis `eᵢ±aᵢ`
transfers independence. This is the carrier-side linear-independence input to `exact_neg_inertia`. -/
theorem multiPair_carrier_linearIndependent {k : ℕ} (t : Fin k → ℂ) (z : Fin (k + k) → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) (hz : Function.Injective z)
    (htz : ∀ i j, t i ≠ z j) (hstz : ∀ i j, star (t i) ≠ z j) :
    LinearIndependent ℂ
      (Sum.elim (fun (i : Fin k) (j : Fin (k + k)) => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹)
                (fun (i : Fin k) (j : Fin (k + k)) => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹)) := by
  classical
  -- the `2k` poles `{t̄ᵢ, tᵢ}` reindexed along `Fin k ⊕ Fin k ≃ Fin (k+k)`
  set σ : Fin k ⊕ Fin k ≃ Fin (k + k) := finSumFinEquiv with hσ
  set P : Fin (k + k) → ℂ := fun e => Sum.elim (fun i => star (t i)) t (σ.symm e) with hP_def
  have Pinl : ∀ i, P (σ (Sum.inl i)) = star (t i) := by
    intro i; rw [hP_def]; simp only [Equiv.symm_apply_apply, Sum.elim_inl]
  have Pinr : ∀ i, P (σ (Sum.inr i)) = t i := by
    intro i; rw [hP_def]; simp only [Equiv.symm_apply_apply, Sum.elim_inr]
  -- the poles are distinct (the conjugates sit in the lower half-plane)
  have hPinj : Function.Injective P := by
    have hels : Function.Injective (Sum.elim (fun i => star (t i)) t) := by
      rw [Sum.elim_injective]
      refine ⟨star_injective.comp htinj, htinj, ?_⟩
      intro a b hcontra
      have him := congrArg Complex.im hcontra
      simp only [Complex.star_def, Complex.conj_im] at him
      have := ht a; have := ht b; linarith
    rw [hP_def]; exact hels.comp σ.symm.injective
  have hPz : ∀ e j, P e ≠ z j := by
    have key : ∀ (s : Fin k ⊕ Fin k) j, Sum.elim (fun i => star (t i)) t s ≠ z j := by
      intro s j
      cases s with
      | inl i => exact hstz i j
      | inr i => exact htz i j
    intro e j; rw [hP_def]; exact key (σ.symm e) j
  -- the reindexed Cauchy family `{eᵢ, aᵢ}` is linearly independent
  have hGeaLI := (cauchy_linearIndependent P z hPinj hz hPz).comp ⇑σ σ.injective
  rw [Fintype.linearIndependent_iff] at hGeaLI
  -- transfer independence across the `[[1,1],[1,−1]]` change of basis
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  have hdzero : ∀ s, (Sum.elim (fun i => c (Sum.inl i) + c (Sum.inr i))
      (fun i => c (Sum.inl i) - c (Sum.inr i))) s = 0 := by
    apply hGeaLI
    rw [← hsum, Fintype.sum_sum_type, Fintype.sum_sum_type,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    funext j
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
               smul_eq_mul]
    rw [Pinl i, Pinr i]
    ring
  intro s
  cases s with
  | inl i =>
      have h1 : c (Sum.inl i) + c (Sum.inr i) = 0 := hdzero (Sum.inl i)
      have h2 : c (Sum.inl i) - c (Sum.inr i) = 0 := hdzero (Sum.inr i)
      have hsplit : c (Sum.inl i)
          = ((c (Sum.inl i) + c (Sum.inr i)) + (c (Sum.inl i) - c (Sum.inr i))) / 2 := by ring
      rw [hsplit, h1, h2]; ring
  | inr i =>
      have h1 : c (Sum.inl i) + c (Sum.inr i) = 0 := hdzero (Sum.inl i)
      have h2 : c (Sum.inl i) - c (Sum.inr i) = 0 := hdzero (Sum.inr i)
      have hsplit : c (Sum.inr i)
          = ((c (Sum.inl i) + c (Sum.inr i)) - (c (Sum.inl i) - c (Sum.inr i))) / 2 := by ring
      rw [hsplit, h1, h2]; ring

/-- **Unconditional exact Krein–Langer inertia `κ₋ = k` for the conjugate-pair carrier.** For `k`
distinct off-line poles `t` (`Im tᵢ > 0`) and `2k` distinct nodes `z` avoiding the poles and their
conjugates, the factored carrier matrix `H = ∑ᵢ wᵢ wᵢ* − ∑ᵢ uᵢ uᵢ*` (with `wᵢ = eᵢ+aᵢ`, `uᵢ = eᵢ−aᵢ`,
`aᵢ(j)=(tᵢ−zⱼ)⁻¹`, `eᵢ(j)=(t̄ᵢ−zⱼ)⁻¹`, equal to `2·multiPairPick`) has negative inertia **exactly `k`**:
every subspace on which `H` is negative-definite has `dim ≤ k`, and one of `dim = k` exists. This
discharges the `hT` surjectivity hypothesis of `KreinLangerInertia.exact_neg_inertia` unconditionally,
by combining `multiPair_carrier_linearIndependent` (the carrier vectors are independent) with
`eval_surjective_of_linearIndependent` (independence ⟹ evaluation map surjective), reindexed across
`Fin k ⊕ Fin k ≃ Fin (k+k)`. It is the quantitative, unconditional finite firewall: `k` off-line zero
pairs force exactly `k` negative directions in the carrier Pick form. Still finite — no infinite
carrier `m_ξ`, no RH. -/
theorem multiPair_carrier_exact_neg_inertia {k : ℕ} (t : Fin k → ℂ) (z : Fin (k + k) → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) (hz : Function.Injective z)
    (htz : ∀ i j, t i ≠ z j) (hstz : ∀ i j, star (t i) ≠ z j)
    (w u : Fin k → (Fin (k + k) → ℂ))
    (hw : w = fun i j => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹)
    (hu : u = fun i j => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹) :
    (∀ W : Submodule ℂ (Fin (k + k) → ℂ),
        (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0)
        → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (k + k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ ((∑ i, Matrix.of (fun p q => w i p * star (w i q)))
           - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))).mulVec y).re < 0) := by
  classical
  set σ : Fin k ⊕ Fin k ≃ Fin (k + k) := finSumFinEquiv with hσ
  -- the two halves of the evaluation map, as linear maps
  set Φ : (Fin (k + k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (w i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a }) with hΦdef
  set Ψ : (Fin (k + k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun y => star (u i) ⬝ᵥ y
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c a => dotProduct_smul c _ a }) with hΨdef
  have hΦ : ∀ (y : Fin (k + k) → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y := fun y i => rfl
  have hΨ : ∀ (y : Fin (k + k) → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y := fun y i => rfl
  -- the carrier family is independent, hence its evaluation map is surjective
  have hLI : LinearIndependent ℂ (Sum.elim w u) := by
    rw [hw, hu]; exact multiPair_carrier_linearIndependent t z ht htinj hz htz hstz
  have hLI' : LinearIndependent ℂ (Sum.elim w u ∘ ⇑σ.symm) := hLI.comp _ σ.symm.injective
  have hEsurj := eval_surjective_of_linearIndependent (Sum.elim w u ∘ ⇑σ.symm) hLI'
  -- discharge the surjectivity hypothesis of `exact_neg_inertia`
  have hT : Function.Surjective (Φ.prod Ψ) := by
    intro ab
    obtain ⟨y, hy⟩ := hEsurj (fun e => Sum.elim ab.1 ab.2 (σ.symm e))
    refine ⟨y, ?_⟩
    have hl : ∀ i, star (w i) ⬝ᵥ y = ab.1 i := by
      intro i
      have hcf := congrFun hy (σ (Sum.inl i))
      simpa [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using hcf
    have hr : ∀ i, star (u i) ⬝ᵥ y = ab.2 i := by
      intro i
      have hcf := congrFun hy (σ (Sum.inr i))
      simpa [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using hcf
    rw [LinearMap.prod_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simpa [hΦ y i] using hl i
    · simpa [hΨ y i] using hr i
  exact exact_neg_inertia w u Φ Ψ hΦ hΨ hT

end

end GaloisForLFunctions
