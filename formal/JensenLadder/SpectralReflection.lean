import JensenLadder.SpectralRealization
import Mathlib.Tactic

/-!
# Functional-equation reflection for exact spectral realizations

An exact regular Hilbert--Pólya / CCM spectral realization must respect the
functional-equation symmetry `z ↦ -z` of `Ξ`: spectral heights occur in
opposite pairs.

`SpectralRealization` already proves the set-level statement: every spectral
height has some opposite spectral height.  This module packages the stronger
carrier-level form used by modular-reflection language:

* a supplied reflection involution on the spectral carrier;
* a canonical noncomputable chosen reflection when the height map is injective.

The injectivity hypothesis is deliberate.  If a spectral model carries
multiplicities, a chosen opposite point need not be canonical or involutive
without extra structure.  This module does not prove the existence of the
spectral realization, CCM convergence, simplicity of zeros, or the Riemann
Hypothesis.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SpectralRealization

universe u

/-- A carrier-level reflection for an exact regular `Ξ` spectral realization.

This records the modular/functional-equation symmetry on the spectral carrier:
`neg` sends a spectral point to an opposite-height spectral point, and does so
involutively.  Supplying such a reflection is structure on a spectral model;
the exact realization itself only gives existence of an opposite-height point. -/
structure RegularSpectralReflection
    (S : RiemannXiRegularSpectralRealization.{u}) where
  neg : S.Spectrum → S.Spectrum
  height_neg : ∀ γ : S.Spectrum, S.height (neg γ) = -S.height γ
  neg_neg : ∀ γ : S.Spectrum, neg (neg γ) = γ

namespace RiemannXiRegularSpectralRealization

/-- A noncanonical opposite-height point obtained from exactness and the
functional equation. -/
noncomputable def negHeightPoint
    (S : RiemannXiRegularSpectralRealization.{u}) (γ : S.Spectrum) :
    S.Spectrum :=
  Classical.choose (exists_neg_height_of_regularSpectralRealization S γ)

/-- The chosen point has the opposite height. -/
theorem height_negHeightPoint
    (S : RiemannXiRegularSpectralRealization.{u}) (γ : S.Spectrum) :
    S.height (S.negHeightPoint γ) = -S.height γ :=
  Classical.choose_spec (exists_neg_height_of_regularSpectralRealization S γ)

/-- If the spectral-height map is injective, the chosen opposite-height map is
an involution.  The injectivity hypothesis rules out multiplicity ambiguity in
the noncanonical choice. -/
theorem negHeightPoint_involutive_of_height_injective
    (S : RiemannXiRegularSpectralRealization.{u})
    (hinj : Function.Injective S.height) :
    ∀ γ : S.Spectrum, S.negHeightPoint (S.negHeightPoint γ) = γ := by
  intro γ
  apply hinj
  rw [height_negHeightPoint, height_negHeightPoint]
  ring

/-- An exact regular spectral realization with injective height map has a
canonical noncomputable carrier-level reflection. -/
noncomputable def regularSpectralReflectionOfInjectiveHeight
    (S : RiemannXiRegularSpectralRealization.{u})
    (hinj : Function.Injective S.height) :
    RegularSpectralReflection S where
  neg := S.negHeightPoint
  height_neg := S.height_negHeightPoint
  neg_neg := S.negHeightPoint_involutive_of_height_injective hinj

end RiemannXiRegularSpectralRealization

namespace RegularSpectralReflection

variable {S : RiemannXiRegularSpectralRealization.{u}}

/-- A reflection-fixed spectral point has height zero. -/
theorem height_eq_zero_of_neg_eq_self
    (R : RegularSpectralReflection S) {γ : S.Spectrum}
    (hfixed : R.neg γ = γ) :
    S.height γ = 0 := by
  have hheight : S.height γ = -S.height γ := by
    simpa [hfixed] using R.height_neg γ
  linarith

/-- If the height map is injective, every zero-height spectral point is fixed by
the reflection. -/
theorem neg_eq_self_of_height_eq_zero
    (R : RegularSpectralReflection S)
    (hinj : Function.Injective S.height) {γ : S.Spectrum}
    (hzero : S.height γ = 0) :
    R.neg γ = γ := by
  apply hinj
  rw [R.height_neg, hzero]
  simp

/-- Under injective heights, reflection-fixed points are exactly the
zero-height spectral points. -/
theorem neg_eq_self_iff_height_eq_zero
    (R : RegularSpectralReflection S)
    (hinj : Function.Injective S.height) (γ : S.Spectrum) :
    R.neg γ = γ ↔ S.height γ = 0 := by
  constructor
  · intro hfixed
    exact height_eq_zero_of_neg_eq_self R hfixed
  · intro hzero
    exact neg_eq_self_of_height_eq_zero R hinj hzero

/-- A nonzero-height point cannot be fixed by the reflection. -/
theorem neg_ne_self_of_height_ne_zero
    (R : RegularSpectralReflection S) {γ : S.Spectrum}
    (hzero : S.height γ ≠ 0) :
    R.neg γ ≠ γ := by
  intro hfixed
  exact hzero (height_eq_zero_of_neg_eq_self R hfixed)

end RegularSpectralReflection

/-- An exact regular `Ξ` spectral realization equipped with a carrier-level
functional-equation reflection.

This is the Lean-facing modular-reflection endpoint.  It still includes exact
regular zero-set soundness and completeness through `realization`; the
reflection field is additional symmetry structure, not a substitute for the
open spectral-identification/convergence theorem. -/
structure ReflectedRegularSpectralRealization where
  realization : RiemannXiRegularSpectralRealization.{u}
  reflection : RegularSpectralReflection realization

namespace ReflectedRegularSpectralRealization

/-- A reflected exact regular spectral realization proves mathlib's
`RiemannHypothesis`.

The reflection is not used in the proof: exact real-height realization is
already RH-strength.  This theorem is deliberately a calibration of the
endpoint, not a proof of the missing non-circular construction. -/
theorem riemannHypothesis
    (S : ReflectedRegularSpectralRealization.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization S.realization

end ReflectedRegularSpectralRealization

/-- The tautological reflection on the canonical regular zero-set realization.

This construction uses the regular `Ξ` zero set as the carrier and is therefore
circular as a proof route.  Its purpose is to calibrate the reflected endpoint:
if the regular zeros are already known to be real, then the functional-equation
reflection `z ↦ -z` acts on the carrier. -/
noncomputable def canonicalRegularSpectralReflectionOfRegularXiZerosReal
    (H : ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0) :
    RegularSpectralReflection
      (canonicalRegularSpectralRealizationOfRegularXiZerosReal H) where
  neg γ := ⟨-γ.1, RHReduction.riemannXiRegularZero_neg γ.1 γ.2⟩
  height_neg := by
    intro γ
    simp [canonicalRegularSpectralRealizationOfRegularXiZerosReal]
  neg_neg := by
    intro γ
    apply Subtype.ext
    simp

/-- The tautological reflected exact regular realization obtained from known
realness of all regular `Ξ` zeros.

This is the reverse direction of the calibration equivalence and is not a
non-circular Hilbert--Pólya/CCM construction. -/
noncomputable def canonicalReflectedRegularSpectralRealizationOfRegularXiZerosReal
    (H : ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0) :
    ReflectedRegularSpectralRealization.{0} where
  realization := canonicalRegularSpectralRealizationOfRegularXiZerosReal H
  reflection := canonicalRegularSpectralReflectionOfRegularXiZerosReal H

/-- The reflected exact regular spectral endpoint is equivalent to mathlib's
`RiemannHypothesis`.

The forward direction is the Hilbert--Pólya reduction.  The reverse direction is
the tautological zero-set construction with its functional-equation reflection,
so this theorem identifies the endpoint's exact strength; it does not construct
the endpoint non-circularly. -/
theorem nonempty_reflectedRegularSpectralRealization_iff_riemannHypothesis :
    Nonempty ReflectedRegularSpectralRealization.{0} ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨S⟩
    exact S.riemannHypothesis
  · intro hRH
    have H : ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
      (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1 hRH
    exact ⟨canonicalReflectedRegularSpectralRealizationOfRegularXiZerosReal H⟩

end SpectralRealization
end JensenLadder
