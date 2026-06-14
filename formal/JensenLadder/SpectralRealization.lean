import JensenLadder.RHReduction

/-!
# Spectral realization interface for the `Ξ` endpoint

This module isolates the exact open input in the Hilbert--Pólya /
Connes--Consani--Moscovici direction:

```text
there is a spectrum with real heights whose points are exactly the zeros of Ξ.
```

If such an exact spectral identification is proved by an external analytic or
operator-theoretic construction, then mathlib's `RiemannHypothesis` follows by
the already formalized `Ξ`-zero reduction in `RHReduction`.

This file does **not** prove the existence of the spectral realization, the
self-adjointness of any operator, the CCM `N,lambda -> infinity` convergence
theorem, or the Riemann Hypothesis.  It records the Lean-facing endpoint that a
non-circular spectral construction must discharge.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SpectralRealization

open Complex

universe u

/-- Soundness of a real-height spectral model for `Ξ`: every listed spectral
height is actually a zero of `Ξ`.  This direction prevents extra spectral points
from being silently treated as zeros. -/
def XiZeroSoundness {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ γ : Spectrum, RHReduction.riemannXi (height γ : ℂ) = 0

/-- Completeness of a real-height spectral model for `Ξ`: every zero of `Ξ`
appears at one of the real spectral heights.  This is the load-bearing direction
for RH, since real heights have imaginary part zero. -/
def XiZeroCompleteness {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXi z = 0 → ∃ γ : Spectrum, z = (height γ : ℂ)

/-- Exactness of a real-height spectral model for `Ξ`: the zero set of `Ξ` is
precisely the range of the real spectral-height map. -/
def XiZeroExact {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXi z = 0 ↔ ∃ γ : Spectrum, z = (height γ : ℂ)

/-- Soundness plus completeness is exactly the zero-set equality expected from a
non-circular spectral realization. -/
theorem xiZeroExact_of_sound_complete {Spectrum : Type u} {height : Spectrum → ℝ}
    (hsound : XiZeroSoundness height)
    (hcomplete : XiZeroCompleteness height) :
    XiZeroExact height := by
  intro z
  constructor
  · exact hcomplete z
  · rintro ⟨γ, rfl⟩
    exact hsound γ

/-- An exact spectral realization of the Riemann `Ξ` zeros by real heights.

The field `height : Spectrum → ℝ` represents the output of a manifestly-real
spectral construction.  The two proof fields say that these heights are exactly
the `Ξ` zeros.  Proving such a structure non-circularly is the open
Hilbert--Pólya / CCM convergence problem; this Lean structure only records the
interface. -/
structure RiemannXiSpectralRealization where
  Spectrum : Type u
  height : Spectrum → ℝ
  sound : XiZeroSoundness height
  complete : XiZeroCompleteness height

/-- The packaged realization really identifies the `Ξ` zero set with its real
spectral heights. -/
theorem xiZeroExact_of_spectralRealization
    (S : RiemannXiSpectralRealization) :
    XiZeroExact S.height :=
  xiZeroExact_of_sound_complete S.sound S.complete

/-- The functional equation makes the `Ξ` zero set invariant under `z ↦ -z`. -/
theorem riemannXi_zero_neg_iff (z : ℂ) :
    RHReduction.riemannXi (-z) = 0 ↔ RHReduction.riemannXi z = 0 := by
  rw [RHReduction.riemannXi_even]

/-- Any exact real-height spectral realization has its height set closed under
negation.  This is the Lean-facing form of the functional-equation reflection
constraint on Hilbert--Pólya / CCM candidates. -/
theorem exists_neg_height_of_spectralRealization
    (S : RiemannXiSpectralRealization) (γ : S.Spectrum) :
    ∃ γ' : S.Spectrum, S.height γ' = -S.height γ := by
  have hz : RHReduction.riemannXi (-(S.height γ : ℂ)) = 0 := by
    rw [RHReduction.riemannXi_even]
    exact S.sound γ
  rcases S.complete (-(S.height γ : ℂ)) hz with ⟨γ', hγ'⟩
  refine ⟨γ', ?_⟩
  exact_mod_cast hγ'.symm

/-- Any exact real-height spectral realization forces all `Ξ` zeros to be real. -/
theorem xi_zeros_real_of_spectralRealization
    (S : RiemannXiSpectralRealization) :
    ∀ z : ℂ, RHReduction.riemannXi z = 0 → z.im = 0 := by
  intro z hz
  rcases S.complete z hz with ⟨γ, rfl⟩
  simp

/-- A non-circular exact spectral realization of `Ξ` zeros by real heights would
prove mathlib's `RiemannHypothesis`.

This is a reduction theorem, not an RH proof: the hypothesis packages the open
spectral-identification/convergence theorem. -/
theorem riemannHypothesis_of_spectralRealization
    (S : RiemannXiSpectralRealization) :
    RiemannHypothesis :=
  RHReduction.riemannHypothesis_of_riemannXi_zeros_real
    (xi_zeros_real_of_spectralRealization S)

/-- The tautological exact spectral realization obtained by taking the spectrum
itself to be the zero set of `Ξ`, once those zeros are known to be real.

This construction is deliberately circular as a route to RH: its carrier is the
zero set of `Ξ`.  Its purpose is to calibrate the interface, showing that an
abstract exact real-height spectral realization is precisely as strong as
realness of the zeros unless a non-circular construction supplies it. -/
noncomputable def canonicalSpectralRealizationOfXiZerosReal
    (H : ∀ z : ℂ, RHReduction.riemannXi z = 0 → z.im = 0) :
    RiemannXiSpectralRealization.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXi z = 0}
  height γ := γ.1.re
  sound := by
    intro γ
    have hzero : RHReduction.riemannXi γ.1 = 0 := γ.2
    have him : γ.1.im = 0 := H γ.1 hzero
    have hγ : ((γ.1.re : ℝ) : ℂ) = γ.1 := by
      apply Complex.ext
      · simp
      · simp [him]
    simpa [hγ] using hzero
  complete := by
    intro z hz
    refine ⟨⟨z, hz⟩, ?_⟩
    have him : z.im = 0 := H z hz
    apply Complex.ext
    · simp
    · simp [him]

/-- The abstract exact real-height spectral-realization interface is equivalent
(at universe `0`) to reality of all `Ξ` zeros.

The forward direction is the useful Hilbert--Pólya reduction.  The reverse
direction is the tautological zero-set construction above, and marks the
anti-circularity requirement: a spectral proof must construct the realization
without first assuming the zeros are real. -/
theorem nonempty_spectralRealization_iff_riemannXi_zeros_real :
    Nonempty RiemannXiSpectralRealization.{0} ↔
      (∀ z : ℂ, RHReduction.riemannXi z = 0 → z.im = 0) := by
  constructor
  · rintro ⟨S⟩
    exact xi_zeros_real_of_spectralRealization S
  · intro H
    exact ⟨canonicalSpectralRealizationOfXiZerosReal H⟩

/-- Equivalently, the abstract exact real-height spectral-realization interface
is the completed-zeta critical-line endpoint. -/
theorem nonempty_spectralRealization_iff_completedZeta_zeros_on_line :
    Nonempty RiemannXiSpectralRealization.{0} ↔
      (∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2) := by
  exact nonempty_spectralRealization_iff_riemannXi_zeros_real.trans
    RHReduction.completedZeta_zeros_on_line_iff_riemannXi_zeros_real.symm

/-!
## Regular zero-set spectral realization

The raw interface above is a strong sufficient endpoint.  The exact
RH-equivalent spectral endpoint is the regular zero set of the raw `Ξ` wrapper,
with the Gamma-factor exceptional set and pole point filtered out as in
`RHReduction.riemannXiRegularZero`.
-/

/-- Soundness of a real-height spectral model for the regular `Ξ` zeros. -/
def RegularXiZeroSoundness {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ γ : Spectrum, RHReduction.riemannXiRegularZero (height γ : ℂ)

/-- Completeness of a real-height spectral model for the regular `Ξ` zeros. -/
def RegularXiZeroCompleteness {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z → ∃ γ : Spectrum, z = (height γ : ℂ)

/-- Exactness of a real-height spectral model for the regular `Ξ` zeros. -/
def RegularXiZeroExact {Spectrum : Type u} (height : Spectrum → ℝ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ↔ ∃ γ : Spectrum, z = (height γ : ℂ)

/-- Soundness plus completeness is exactness for the regular zero set. -/
theorem regularXiZeroExact_of_sound_complete {Spectrum : Type u} {height : Spectrum → ℝ}
    (hsound : RegularXiZeroSoundness height)
    (hcomplete : RegularXiZeroCompleteness height) :
    RegularXiZeroExact height := by
  intro z
  constructor
  · exact hcomplete z
  · rintro ⟨γ, rfl⟩
    exact hsound γ

/-- An exact spectral realization of the regular `Ξ` zeros by real heights.

This is the precise Hilbert--Pólya / CCM endpoint for mathlib's
`RiemannHypothesis`.  Proving this structure non-circularly is still the open
spectral-identification problem. -/
structure RiemannXiRegularSpectralRealization where
  Spectrum : Type u
  height : Spectrum → ℝ
  sound : RegularXiZeroSoundness height
  complete : RegularXiZeroCompleteness height

/-- The packaged regular realization identifies the regular `Ξ` zero set. -/
theorem regularXiZeroExact_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization) :
    RegularXiZeroExact S.height :=
  regularXiZeroExact_of_sound_complete S.sound S.complete

/-- Exact real-height data for the regular `Ξ` zero set already forces all
regular zeros to be real.

This is a reduction endpoint, not an existence theorem: the hypothesis is the
open spectral-identification/convergence statement. -/
theorem regular_xi_zeros_real_of_regularXiZeroExact
    {Spectrum : Type u} {height : Spectrum → ℝ}
    (hexact : RegularXiZeroExact height) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  rcases (hexact z).1 hz with ⟨γ, rfl⟩
  simp

/-- A non-circular proof of exact regular `Ξ` spectral data by real heights
would prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_regularXiZeroExact
    {Spectrum : Type u} {height : Spectrum → ℝ}
    (hexact : RegularXiZeroExact height) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (regular_xi_zeros_real_of_regularXiZeroExact hexact)

/-- Package exact regular zero-set data as the regular spectral-realization
structure.

This adapter does not construct the spectral data; it only translates a
zero-set equality into the structure consumed by downstream reductions. -/
def regularSpectralRealizationOfRegularXiZeroExact
    {Spectrum : Type u} (height : Spectrum → ℝ)
    (hexact : RegularXiZeroExact height) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := Spectrum
  height := height
  sound := by
    intro γ
    exact (hexact (height γ : ℂ)).2 ⟨γ, rfl⟩
  complete := by
    intro z hz
    exact (hexact z).1 hz

/-- Exact regular zero-set data supplies a packaged regular spectral
realization at the same universe level. -/
theorem nonempty_regularSpectralRealization_of_regularXiZeroExact
    {Spectrum : Type u} {height : Spectrum → ℝ}
    (hexact : RegularXiZeroExact height) :
    Nonempty RiemannXiRegularSpectralRealization.{u} :=
  ⟨regularSpectralRealizationOfRegularXiZeroExact height hexact⟩

/-- Any exact real-height spectral realization of the regular `Ξ` zeros has its
height set closed under negation.  This is the regular-zero version of the
functional-equation reflection constraint. -/
theorem exists_neg_height_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization) (γ : S.Spectrum) :
    ∃ γ' : S.Spectrum, S.height γ' = -S.height γ := by
  have hz : RHReduction.riemannXiRegularZero (-(S.height γ : ℂ)) := by
    exact (RHReduction.riemannXiRegularZero_neg_iff (S.height γ : ℂ)).2 (S.sound γ)
  rcases S.complete (-(S.height γ : ℂ)) hz with ⟨γ', hγ'⟩
  refine ⟨γ', ?_⟩
  exact_mod_cast hγ'.symm

/-- Any exact real-height spectral realization of the regular `Ξ` zeros forces
those zeros to be real. -/
theorem regular_xi_zeros_real_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  rcases S.complete z hz with ⟨γ, rfl⟩
  simp

/-- A non-circular exact spectral realization of the regular `Ξ` zeros would
prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_regularSpectralRealization
    (S : RiemannXiRegularSpectralRealization) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (regular_xi_zeros_real_of_regularSpectralRealization S)

/-- The tautological exact regular spectral realization obtained by taking the
spectrum itself to be the regular zero set.

As with the raw zero-set construction, this is deliberately circular as a proof
route.  It calibrates the interface and marks the anti-circularity requirement
for any analytic operator construction. -/
noncomputable def canonicalRegularSpectralRealizationOfRegularXiZerosReal
    (H : ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0) :
    RiemannXiRegularSpectralRealization.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXiRegularZero z}
  height γ := γ.1.re
  sound := by
    intro γ
    have hreg : RHReduction.riemannXiRegularZero γ.1 := γ.2
    have him : γ.1.im = 0 := H γ.1 hreg
    have hγ : ((γ.1.re : ℝ) : ℂ) = γ.1 := by
      apply Complex.ext
      · simp
      · simp [him]
    simpa [hγ] using hreg
  complete := by
    intro z hz
    refine ⟨⟨z, hz⟩, ?_⟩
    have him : z.im = 0 := H z hz
    apply Complex.ext
    · simp
    · simp [him]

/-- The exact regular spectral-realization interface is equivalent to reality of
all regular `Ξ` zeros. -/
theorem nonempty_regularSpectralRealization_iff_regular_riemannXi_zeros_real :
    Nonempty RiemannXiRegularSpectralRealization.{0} ↔
      (∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0) := by
  constructor
  · rintro ⟨S⟩
    exact regular_xi_zeros_real_of_regularSpectralRealization S
  · intro H
    exact ⟨canonicalRegularSpectralRealizationOfRegularXiZerosReal H⟩

/-- The exact regular spectral-realization interface is equivalent to mathlib's
`RiemannHypothesis`.

The forward direction is the Hilbert--Pólya reduction.  The reverse direction is
the tautological zero-set realization, so it is not a proof method; it only
shows that the interface has exactly RH strength. -/
theorem nonempty_regularSpectralRealization_iff_riemannHypothesis :
    Nonempty RiemannXiRegularSpectralRealization.{0} ↔ RiemannHypothesis := by
  exact nonempty_regularSpectralRealization_iff_regular_riemannXi_zeros_real.trans
    RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real.symm

/-!
## Squared spectral faithfulness

Some scaling/prolate operator candidates naturally represent a zero `z` by the
real spectral value `-z^2`, rather than by the height `z` itself.  In that
interface, self-adjointness only supplies real spectral values; the
load-bearing open input is *faithfulness*: every regular `Ξ` zero must actually
be represented by such a real spectral value.  The algebra below records that
this is sufficient for RH once the central case `z.re = 0` is separately
excluded.

This is still a reduction endpoint.  It does not construct the operator, prove
faithfulness, or prove the no-central-zero side condition.
-/

/-- One-dimensional side gate for the squared-spectrum endpoint: the completed
zeta function has no real regular zero inside the critical strip.

The outside-strip real-axis cases are discharged below using the functional
equation and mathlib's nonvanishing theorem on `Re s ≥ 1`; the open real-axis
piece is isolated to `0 < x < 1`. -/
def NoRealCriticalStripCompletedZetaZero : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → completedRiemannZeta (x : ℂ) = 0 → False

/-- There are no regular `Ξ` zeros on the central axis of the squared spectral
coordinate.  This is the side condition needed because `-z^2` can be real either
when `z.im = 0` or when `z.re = 0`. -/
def NoCentralRegularXiZero : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.re ≠ 0

/-- The real critical-strip nonvanishing side gate excludes central regular
`Ξ` zeros.

If a central-axis regular `Ξ` zero existed, the corresponding completed-zeta
zero would lie on the real axis.  For `x ≥ 1`, mathlib's
`riemannZeta_ne_zero_of_one_le_re` gives a contradiction.  For `x ≤ 0`, the
functional equation reflects it to `1 - x ≥ 1`.  Thus only the real interval
`0 < x < 1` is a separate input. -/
theorem noCentralRegularXiZero_of_noRealCriticalStripCompletedZetaZero
    (hstrip : NoRealCriticalStripCompletedZetaZero) :
    NoCentralRegularXiZero := by
  intro z hz hzre
  rcases hz with ⟨hXi, _hG, _hne1⟩
  let x : ℝ := (1 / 2 + Complex.I * z).re
  have hs_eq : ((x : ℝ) : ℂ) = 1 / 2 + Complex.I * z := by
    apply Complex.ext
    · simp [x]
    · simp [x, hzre]
  have hΛx : completedRiemannZeta (x : ℂ) = 0 := by
    rw [hs_eq]
    simpa [RHReduction.riemannXi] using hXi
  by_cases hx0 : 0 < x
  · by_cases hx1 : x < 1
    · exact hstrip x hx0 hx1 hΛx
    · have hxge1 : 1 ≤ x := le_of_not_gt hx1
      have hx_ne0 : (x : ℂ) ≠ 0 := by
        intro hxzero
        have hx_real_zero : x = 0 := by exact_mod_cast hxzero
        linarith
      have hzeta : riemannZeta (x : ℂ) = 0 := by
        rw [riemannZeta_def_of_ne_zero hx_ne0, hΛx, zero_div]
      exact (riemannZeta_ne_zero_of_one_le_re (s := (x : ℂ)) (by simpa using hxge1)) hzeta
  · have hxle0 : x ≤ 0 := le_of_not_gt hx0
    let y : ℝ := 1 - x
    have hyge1 : 1 ≤ y := by dsimp [y]; linarith
    have hy_ne0 : (y : ℂ) ≠ 0 := by
      intro hyzero
      have hy_real_zero : y = 0 := by exact_mod_cast hyzero
      linarith
    have hΛy : completedRiemannZeta (y : ℂ) = 0 := by
      have hFE : completedRiemannZeta (1 - (x : ℂ)) =
          completedRiemannZeta (x : ℂ) :=
        completedRiemannZeta_one_sub (x : ℂ)
      have hy_eq : (y : ℂ) = 1 - (x : ℂ) := by simp [y]
      rw [hy_eq, hFE]
      exact hΛx
    have hzeta : riemannZeta (y : ℂ) = 0 := by
      rw [riemannZeta_def_of_ne_zero hy_ne0, hΛy, zero_div]
    exact (riemannZeta_ne_zero_of_one_le_re (s := (y : ℂ)) (by simpa [y] using hyge1)) hzeta

/-- A central regular `Ξ`-zero exclusion is exactly the real critical-strip
completed-zeta nonvanishing side gate.

This is the converse of `noCentralRegularXiZero_of_noRealCriticalStripCompletedZetaZero`:
a real completed-zeta zero with `0 < x < 1` gives a regular `Ξ` zero at the
pure-imaginary coordinate `z = -i * (x - 1/2)`, hence violates
`NoCentralRegularXiZero`. -/
theorem noRealCriticalStripCompletedZetaZero_of_noCentralRegularXiZero
    (hnoncentral : NoCentralRegularXiZero) :
    NoRealCriticalStripCompletedZetaZero := by
  intro x hx0 hx1 hΛ
  let z : ℂ := -Complex.I * ((x : ℂ) - 1 / 2)
  have hscoord : 1 / 2 + Complex.I * z = (x : ℂ) := by
    dsimp [z]
    have hII : Complex.I * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    calc
      1 / 2 + Complex.I * (-Complex.I * ((x : ℂ) - 1 / 2))
          = 1 / 2 + Complex.I * (-Complex.I) * ((x : ℂ) - 1 / 2) := by ring
      _ = 1 / 2 + 1 * ((x : ℂ) - 1 / 2) := by rw [hII]
      _ = (x : ℂ) := by ring
  have hzre : z.re = 0 := by
    dsimp [z]
    simp
  have hG : Gammaℝ (x : ℂ) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    cases n with
    | zero =>
        have hxzeroC : (x : ℂ) = 0 := by simpa using hn
        have hxzero : x = 0 := by exact_mod_cast hxzeroC
        linarith
    | succ m =>
        have hxnegC : (x : ℂ) = (-(2 * (m + 1 : ℝ)) : ℂ) := by
          push_cast at hn
          simpa [mul_comm, mul_left_comm, mul_assoc] using hn
        have hxneg : x = -(2 * (m + 1 : ℝ)) := by exact_mod_cast hxnegC
        have hmnonneg : (0 : ℝ) ≤ (m + 1 : ℝ) := by positivity
        have hxnonpos : x ≤ 0 := by
          rw [hxneg]
          nlinarith
        linarith
  have hne1 : (x : ℂ) ≠ 1 := by
    intro hxeq
    have hxreal : x = 1 := by exact_mod_cast hxeq
    linarith
  have hreg : RHReduction.riemannXiRegularZero z := by
    refine ⟨?_, ?_, ?_⟩
    · unfold RHReduction.riemannXi
      rw [hscoord]
      exact hΛ
    · rw [hscoord]
      exact hG
    · rw [hscoord]
      exact hne1
  exact hnoncentral z hreg hzre

/-- The central-axis squared-spectrum side condition is equivalent to the
absence of real completed-zeta zeros in the open critical strip. -/
theorem noCentralRegularXiZero_iff_noRealCriticalStripCompletedZetaZero :
    NoCentralRegularXiZero ↔ NoRealCriticalStripCompletedZetaZero := by
  constructor
  · exact noRealCriticalStripCompletedZetaZero_of_noCentralRegularXiZero
  · exact noCentralRegularXiZero_of_noRealCriticalStripCompletedZetaZero

/-- Faithfulness of a squared real-spectrum model: every regular `Ξ` zero is
represented by the real spectral value `-z^2`.

The map `energy : Spectrum → ℝ` encodes the real spectrum supplied by a
self-adjoint operator.  Extra spectral points are harmless here; the RH-bearing
direction is completeness/faithfulness for zeros. -/
def RegularXiSquaredFaithfulness {Spectrum : Type u} (energy : Spectrum → ℝ) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z → ∃ γ : Spectrum, -z ^ 2 = (energy γ : ℂ)

/-- If `-z^2` is real and `z` is not on the central axis, then `z` lies on the
critical-line axis in the `Ξ` coordinate. -/
theorem im_eq_zero_of_neg_sq_eq_real {z : ℂ} {E : ℝ}
    (hzre : z.re ≠ 0) (hE : -z ^ 2 = (E : ℂ)) :
    z.im = 0 := by
  have him : (-z ^ 2).im = 0 := by
    rw [hE]
    simp
  simp [pow_two] at him
  have hprod : z.re * z.im = 0 := by nlinarith
  exact (mul_eq_zero.mp hprod).resolve_left hzre

/-- Squared-spectrum faithfulness plus the no-central-zero side condition forces
all regular `Ξ` zeros to be real. -/
theorem regular_xi_zeros_real_of_squaredFaithfulness
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hnoncentral : NoCentralRegularXiZero)
    (hfaithful : RegularXiSquaredFaithfulness energy) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  rcases hfaithful z hz with ⟨γ, hγ⟩
  exact im_eq_zero_of_neg_sq_eq_real (hnoncentral z hz) hγ

/-- A non-circular squared spectral faithfulness theorem, together with the
central-axis exclusion, would prove mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_squaredFaithfulness
    {Spectrum : Type u} {energy : Spectrum → ℝ}
    (hnoncentral : NoCentralRegularXiZero)
    (hfaithful : RegularXiSquaredFaithfulness energy) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (regular_xi_zeros_real_of_squaredFaithfulness hnoncentral hfaithful)

/-- Packaged squared-spectrum endpoint for self-adjoint scaling/prolate
operator candidates.

The real-valued `energy` field is the part supplied by self-adjointness.  The
fields `noncentral` and `faithful` are the actual proof obligations before this
interface can imply RH. -/
structure RiemannXiSquaredSpectralFaithfulness where
  Spectrum : Type u
  energy : Spectrum → ℝ
  noncentral : NoCentralRegularXiZero
  faithful : RegularXiSquaredFaithfulness energy

/-- The packaged squared-spectrum endpoint forces regular `Ξ` zeros to be real. -/
theorem regular_xi_zeros_real_of_squaredSpectralFaithfulness
    (S : RiemannXiSquaredSpectralFaithfulness.{u}) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
  regular_xi_zeros_real_of_squaredFaithfulness S.noncentral S.faithful

/-- A non-circular proof of the packaged squared-spectrum endpoint would prove
mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_squaredSpectralFaithfulness
    (S : RiemannXiSquaredSpectralFaithfulness.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_squaredFaithfulness S.noncentral S.faithful

/-- The tautological squared-spectrum endpoint obtained from known RH and the
real critical-strip side gate.

This construction uses the regular `Ξ` zero set itself as the carrier, so it is
circular as a proof route.  It calibrates the squared-spectrum interface:
faithful real squared-spectrum data has exactly the strength of RH plus the
central-axis side gate. -/
noncomputable def canonicalSquaredSpectralFaithfulnessOfRHAndNoRealStrip
    (hRH : RiemannHypothesis)
    (hstrip : NoRealCriticalStripCompletedZetaZero) :
    RiemannXiSquaredSpectralFaithfulness.{0} where
  Spectrum := {z : ℂ // RHReduction.riemannXiRegularZero z}
  energy γ := (-γ.1 ^ 2).re
  noncentral := noCentralRegularXiZero_of_noRealCriticalStripCompletedZetaZero hstrip
  faithful := by
    intro z hz
    refine ⟨⟨z, hz⟩, ?_⟩
    have H : ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
      (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).1 hRH
    have hz_im : z.im = 0 := H z hz
    apply Complex.ext
    · simp
    · simp [pow_two, hz_im]

/-- The squared-spectrum endpoint is equivalent to RH plus the real-strip side
gate.

The forward direction is the useful spectral reduction.  The reverse direction
is the tautological zero-set construction above, so it is only a calibration of
the endpoint's exact strength. -/
theorem nonempty_squaredSpectralFaithfulness_iff_riemannHypothesis_and_noRealStrip :
    Nonempty RiemannXiSquaredSpectralFaithfulness.{0} ↔
      RiemannHypothesis ∧ NoRealCriticalStripCompletedZetaZero := by
  constructor
  · rintro ⟨S⟩
    exact ⟨riemannHypothesis_of_squaredSpectralFaithfulness S,
      (noCentralRegularXiZero_iff_noRealCriticalStripCompletedZetaZero).1 S.noncentral⟩
  · rintro ⟨hRH, hstrip⟩
    exact ⟨canonicalSquaredSpectralFaithfulnessOfRHAndNoRealStrip hRH hstrip⟩

end SpectralRealization
end JensenLadder
