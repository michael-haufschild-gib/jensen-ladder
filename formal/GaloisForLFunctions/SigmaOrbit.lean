import GaloisForLFunctions.Core

/-!
# The σ–reality composite and the critical line as its fixed locus (Tier A)

Formalizes Theorem 1 of `docs/drafts/rh-byproduct-secular-hankel-overdetermination.md` and
`docs/drafts/secular-positivity-hierarchy.md` §1, in its cleanest elementary form: the
functional-equation involution `σ : s ↦ 1 - s` composed with complex conjugation fixes `s`
**exactly on the critical line**. Equivalently, `σ` acts on `s` as complex conjugation iff
`Re s = 1/2` — the `σ`-real / BPS characterization of the critical line, from the
difference-Galois side. It complements the modulus characterization
`GaloisForLFunctions.norm_cpow_eq_critical_iff`.

This is elementary complex arithmetic. No zero, no RH, no positivity, and no conjecture of the
field is formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The functional-equation involution `σ` composed with complex conjugation, `s ↦ 1 - s̄`. -/
def sigmaConj (s : ℂ) : ℂ := sigma ((starRingEnd ℂ) s)

@[simp] theorem sigmaConj_apply (s : ℂ) : sigmaConj s = 1 - (starRingEnd ℂ) s := by
  simp [sigmaConj, sigma]

/-- `σ ∘ conj` is an involution on the `s`-plane. -/
theorem sigmaConj_involutive (s : ℂ) : sigmaConj (sigmaConj s) = s := by
  rw [sigmaConj_apply, sigmaConj_apply, map_sub, map_one, Complex.conj_conj]
  ring

/-- **The critical line is the fixed locus of `σ ∘ conj`.** The FE-conjugate `1 - s̄` equals `s`
iff `Re s = 1/2`; i.e. `σ` acts on `s` as complex conjugation exactly on the critical line. -/
theorem sigmaConj_fixed_iff_critical (s : ℂ) : sigmaConj s = s ↔ s.re = 1 / 2 := by
  rw [sigmaConj_apply, Complex.ext_iff, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨hre, _⟩
    linarith
  · intro h
    exact ⟨by linarith, by ring⟩

end

end GaloisForLFunctions
