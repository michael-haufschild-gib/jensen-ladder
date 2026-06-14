import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Suzuki phase parity algebra

This module formalizes only the algebraic parity selector behind the
Suzuki boundary function after an external deficiency-reflection input has
identified

```text
  V_-(z) = c * V_+(-z).
```

With `phase` standing for `e^{i theta}`, the abstract boundary function is

```text
  W(z) = (z - i) V(z) + phase * c * (z + i) V(-z).
```

The odd branch is selected by `phase * c = 1`; the even branch is selected by
`phase * c = -1`.  When the supplied reflection scalar is unitary, both selected
branches are unit-circle phases.  Converse statements require explicit nonzero
probe hypotheses, because parity at a degenerate probe does not determine the
phase.

The last block records the equally algebraic parity of Suzuki's conjectural
limit target: an even numerator divided by an odd denominator, with the even
factor `z^2`, gives an odd expression.  It is a parity identity for the
field-valued expression only; it does not prove holomorphy, nonvanishing of the
denominator, convergence, or any `xi` derivative theorem.

The calculus bridge below records only the abstract parity fact that the
derivative of an even complex function is odd.  It does not instantiate `xi`,
prove the functional equation or differentiability for `xi`, or prove Suzuki's
limiting denominator/convergence claims.

This file does not prove the deficiency-reflection identity, `|c| = 1`,
existence of a canonical `theta(a)`, convergence in Suzuki's limiting
corollary, or RH.  It is a formal/certificate artifact for the phase-selection
algebra only.  Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SuzukiPhase

/-- Abstract Suzuki boundary function after using a deficiency reflection
`V_-(z) = c * V_+(-z)`.  The scalar `phase` stands for `e^{i theta}`. -/
noncomputable def suzukiW (V : ℂ → ℂ) (phase c z : ℂ) : ℂ :=
  (z - Complex.I) * V z + phase * c * (z + Complex.I) * V (-z)

/-- Raw two-deficiency-function Suzuki boundary expression before substituting
the reflection relation between `V_+` and `V_-`. -/
noncomputable def rawSuzukiW (Vplus Vminus : ℂ → ℂ) (phase z : ℂ) : ℂ :=
  (z - Complex.I) * Vplus z + phase * (z + Complex.I) * Vminus z

/-- Supplied deficiency-reflection relation `V_-(z)=c*V_+(-z)`.

This file treats the relation as input; it does not prove the operator-theoretic
reflection statement or `|c| = 1`. -/
def DeficiencyReflection (Vplus Vminus : ℂ → ℂ) (c : ℂ) : Prop :=
  ∀ z : ℂ, Vminus z = c * Vplus (-z)

/-- A scalar lies on the complex unit circle.

This is the algebraic legality condition for using a complex scalar as a
boundary phase.  It is written with `star` so the lemmas stay purely algebraic
and do not depend on choosing a real argument. -/
def UnitPhase (phase : ℂ) : Prop :=
  phase * star phase = 1

/-- Reflection in the Suzuki height variable. -/
noncomputable def reflectedFunction (V : ℂ → ℂ) : ℂ → ℂ :=
  fun z => V (-z)

/-- Abstract scalar law for a squared complex norm.

For the intended Suzuki deficiency vectors, this is the algebraic shadow of
`‖c • v‖² = c * star c * ‖v‖²`.  The actual Hilbert-space norm and its
domain/completion properties are deliberately external to this file. -/
def ScalarNormScaling (normSq : (ℂ → ℂ) → ℂ) : Prop :=
  ∀ (c : ℂ) (V : ℂ → ℂ),
    normSq (fun z => c * V z) = c * star c * normSq V

/-- Abstract reflection invariance for a squared norm. -/
def ReflectionNormInvariant (normSq : (ℂ → ℂ) → ℂ) : Prop :=
  ∀ V : ℂ → ℂ, normSq (reflectedFunction V) = normSq V

/-- Normalized deficiency-reflection data forces the reflection scalar to be a
unit-circle phase.

This is the operator-theoretic socket behind the `|c|=1` claim: once a concrete
Suzuki Hilbert space supplies scalar norm scaling, reflection norm invariance,
and normalized `V_+`, `V_-`, the scalar in `V_-(z)=cV_+(-z)` is unitary. -/
theorem unitPhase_of_deficiencyReflection_normalized_norm
    (normSq : (ℂ → ℂ) → ℂ) {Vplus Vminus : ℂ → ℂ} {c : ℂ}
    (hscale : ScalarNormScaling normSq)
    (hreflectNorm : ReflectionNormInvariant normSq)
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hplus : normSq Vplus = 1)
    (hminus : normSq Vminus = 1) :
    UnitPhase c := by
  rw [UnitPhase]
  have hfun : Vminus = fun z : ℂ => c * reflectedFunction Vplus z := by
    funext z
    exact hreflect z
  have hnorm : normSq Vminus = c * star c := by
    rw [hfun, hscale, hreflectNorm, hplus]
    ring
  rw [hminus] at hnorm
  exact hnorm.symm

/-- Under a supplied deficiency reflection, the reflection scalar is recovered
from any nonzero pointwise ratio `V_-(z) / V_+(-z)`.

This is the formal version of the `c(a)` x-independence sanity gate: if the
operator-theoretic reflection relation holds, every legal probe gives the same
scalar. -/
theorem reflectionScalar_eq_ratio_at
    (Vplus Vminus : ℂ → ℂ) {c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hden : Vplus (-z) ≠ 0) :
    c = Vminus z / Vplus (-z) := by
  exact (by
    rw [hreflect z]
    field_simp [hden] : Vminus z / Vplus (-z) = c).symm

/-- Computational orientation of `reflectionScalar_eq_ratio_at`. -/
theorem reflectionRatio_eq_reflectionScalar_at
    (Vplus Vminus : ℂ → ℂ) {c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hden : Vplus (-z) ≠ 0) :
    Vminus z / Vplus (-z) = c := by
  rw [hreflect z]
  field_simp [hden]

/-- Under a supplied deficiency reflection, all nonzero pointwise ratios agree. -/
theorem reflectionRatio_constant
    (Vplus Vminus : ℂ → ℂ) {c z w : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hz : Vplus (-z) ≠ 0)
    (hw : Vplus (-w) ≠ 0) :
    Vminus z / Vplus (-z) = Vminus w / Vplus (-w) := by
  rw [reflectionRatio_eq_reflectionScalar_at Vplus Vminus hreflect hz,
    reflectionRatio_eq_reflectionScalar_at Vplus Vminus hreflect hw]

/-- Substituting the supplied deficiency-reflection relation turns the raw
Suzuki boundary expression into `suzukiW`. -/
theorem rawSuzukiW_eq_suzukiW_of_deficiencyReflection
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c) :
    rawSuzukiW Vplus Vminus phase z = suzukiW Vplus phase c z := by
  simp [rawSuzukiW, suzukiW, hreflect z]
  ring

/-- Probe controlling uniqueness of the odd phase branch at a point. -/
noncomputable def oddProbe (V : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - Complex.I) * V z - (z + Complex.I) * V (-z)

/-- Probe controlling uniqueness of the even phase branch at a point. -/
noncomputable def evenProbe (V : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - Complex.I) * V z + (z + Complex.I) * V (-z)

/-- The algebraic odd-branch phase selected by a nonzero reflection scalar `c`. -/
noncomputable def oddPhaseOfReflection (c : ℂ) : ℂ :=
  c⁻¹

/-- The algebraic even-branch phase selected by a nonzero reflection scalar `c`. -/
noncomputable def evenPhaseOfReflection (c : ℂ) : ℂ :=
  -c⁻¹

/-- A unit-circle phase is nonzero. -/
theorem unitPhase_ne_zero {phase : ℂ} (hphase : UnitPhase phase) :
    phase ≠ 0 := by
  intro hzero
  rw [UnitPhase, hzero] at hphase
  norm_num at hphase

/-- The inverse of a unit-circle phase is again a unit-circle phase. -/
theorem unitPhase_inv {phase : ℂ} (hphase : UnitPhase phase) :
    UnitPhase phase⁻¹ := by
  rw [UnitPhase] at hphase ⊢
  rw [star_inv₀]
  have hrev : star phase * phase = 1 := by
    rw [mul_comm]
    exact hphase
  calc
    phase⁻¹ * (star phase)⁻¹ = (star phase * phase)⁻¹ := by
      rw [mul_inv_rev]
    _ = 1 := by rw [hrev, inv_one]

/-- Negating a unit-circle phase stays on the unit circle. -/
theorem unitPhase_neg {phase : ℂ} (hphase : UnitPhase phase) :
    UnitPhase (-phase) := by
  rw [UnitPhase] at hphase ⊢
  rw [star_neg]
  calc
    (-phase) * -star phase = phase * star phase := by ring
    _ = 1 := hphase

/-- The selected odd-branch reflection phase is unitary whenever the reflection
scalar is unitary. -/
theorem oddPhaseOfReflection_unitPhase {c : ℂ}
    (hc : UnitPhase c) :
    UnitPhase (oddPhaseOfReflection c) := by
  simpa [oddPhaseOfReflection] using unitPhase_inv hc

/-- The selected even-branch reflection phase is unitary whenever the reflection
scalar is unitary. -/
theorem evenPhaseOfReflection_unitPhase {c : ℂ}
    (hc : UnitPhase c) :
    UnitPhase (evenPhaseOfReflection c) := by
  simpa [evenPhaseOfReflection] using unitPhase_neg (unitPhase_inv hc)

/-- If the deficiency-reflection scalar is unitary, then every nonzero
pointwise reflection ratio is a unit-circle phase. -/
theorem reflectionRatio_unitPhase_at
    (Vplus Vminus : ℂ → ℂ) {c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : UnitPhase c)
    (hden : Vplus (-z) ≠ 0) :
    UnitPhase (Vminus z / Vplus (-z)) := by
  have hratio : Vminus z / Vplus (-z) = c :=
    reflectionRatio_eq_reflectionScalar_at Vplus Vminus hreflect hden
  simpa [hratio] using hc

/-- The selected odd-branch phase satisfies `phase * c = 1`. -/
theorem oddPhaseOfReflection_mul_reflection_eq_one
    {c : ℂ}
    (hc : c ≠ 0) :
    oddPhaseOfReflection c * c = 1 := by
  simpa [oddPhaseOfReflection] using inv_mul_cancel₀ hc

/-- The selected even-branch phase satisfies `phase * c = -1`. -/
theorem evenPhaseOfReflection_mul_reflection_eq_neg_one
    {c : ℂ}
    (hc : c ≠ 0) :
    evenPhaseOfReflection c * c = -1 := by
  rw [evenPhaseOfReflection]
  calc
    -c⁻¹ * c = -(c⁻¹ * c) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ hc]

/-- Any nonzero reflection scalar has a unique odd-branch phase. -/
theorem phase_eq_oddPhaseOfReflection_of_phase_mul_reflection_eq_one
    {phase c : ℂ}
    (hc : c ≠ 0)
    (hphase : phase * c = 1) :
    phase = oddPhaseOfReflection c := by
  rw [oddPhaseOfReflection]
  calc
    phase = phase * 1 := by ring
    _ = phase * (c * c⁻¹) := by rw [mul_inv_cancel₀ hc]
    _ = (phase * c) * c⁻¹ := by ring
    _ = 1 * c⁻¹ := by rw [hphase]
    _ = c⁻¹ := by ring

/-- Any nonzero reflection scalar has a unique even-branch phase. -/
theorem phase_eq_evenPhaseOfReflection_of_phase_mul_reflection_eq_neg_one
    {phase c : ℂ}
    (hc : c ≠ 0)
    (hphase : phase * c = -1) :
    phase = evenPhaseOfReflection c := by
  rw [evenPhaseOfReflection]
  calc
    phase = phase * 1 := by ring
    _ = phase * (c * c⁻¹) := by rw [mul_inv_cancel₀ hc]
    _ = (phase * c) * c⁻¹ := by ring
    _ = (-1) * c⁻¹ := by rw [hphase]
    _ = -c⁻¹ := by ring

/-- The odd parity branch: if `phase * c = 1`, the abstract Suzuki boundary
function is odd. -/
theorem suzukiW_odd_of_phase_mul_reflection_eq_one
    (V : ℂ → ℂ) {phase c : ℂ}
    (hphase : phase * c = 1) :
    ∀ z : ℂ, suzukiW V phase c (-z) = -suzukiW V phase c z := by
  intro z
  simp [suzukiW, hphase]
  ring

/-- The selected odd-branch phase makes the abstract Suzuki boundary function odd. -/
theorem suzukiW_odd_of_oddPhaseOfReflection
    (V : ℂ → ℂ) {c : ℂ}
    (hc : c ≠ 0) :
    ∀ z : ℂ,
      suzukiW V (oddPhaseOfReflection c) c (-z) =
        -suzukiW V (oddPhaseOfReflection c) c z :=
  suzukiW_odd_of_phase_mul_reflection_eq_one V
    (oddPhaseOfReflection_mul_reflection_eq_one hc)

/-- The even parity branch: if `phase * c = -1`, the abstract Suzuki boundary
function is even. -/
theorem suzukiW_even_of_phase_mul_reflection_eq_neg_one
    (V : ℂ → ℂ) {phase c : ℂ}
    (hphase : phase * c = -1) :
    ∀ z : ℂ, suzukiW V phase c (-z) = suzukiW V phase c z := by
  intro z
  simp [suzukiW, hphase]
  ring

/-- The selected even-branch phase makes the abstract Suzuki boundary function even. -/
theorem suzukiW_even_of_evenPhaseOfReflection
    (V : ℂ → ℂ) {c : ℂ}
    (hc : c ≠ 0) :
    ∀ z : ℂ,
      suzukiW V (evenPhaseOfReflection c) c (-z) =
        suzukiW V (evenPhaseOfReflection c) c z :=
  suzukiW_even_of_phase_mul_reflection_eq_neg_one V
    (evenPhaseOfReflection_mul_reflection_eq_neg_one hc)

/-- Raw odd branch after a supplied deficiency reflection. -/
theorem rawSuzukiW_odd_of_phase_mul_reflection_eq_one
    (Vplus Vminus : ℂ → ℂ) {phase c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hphase : phase * c = 1) :
    ∀ z : ℂ, rawSuzukiW Vplus Vminus phase (-z) = -rawSuzukiW Vplus Vminus phase z := by
  intro z
  rw [rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
  rw [rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
  exact suzukiW_odd_of_phase_mul_reflection_eq_one Vplus hphase z

/-- Raw odd branch for the selected reflection phase. -/
theorem rawSuzukiW_odd_of_oddPhaseOfReflection
    (Vplus Vminus : ℂ → ℂ) {c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : c ≠ 0) :
    ∀ z : ℂ,
      rawSuzukiW Vplus Vminus (oddPhaseOfReflection c) (-z) =
        -rawSuzukiW Vplus Vminus (oddPhaseOfReflection c) z :=
  rawSuzukiW_odd_of_phase_mul_reflection_eq_one Vplus Vminus hreflect
    (oddPhaseOfReflection_mul_reflection_eq_one hc)

/-- A unitary reflection scalar supplies a legal unit-circle odd phase and makes
the raw Suzuki boundary expression odd. -/
theorem oddPhase_unitPhase_and_rawSuzukiW_odd
    (Vplus Vminus : ℂ → ℂ) {c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : UnitPhase c) :
    UnitPhase (oddPhaseOfReflection c) ∧
      ∀ z : ℂ,
        rawSuzukiW Vplus Vminus (oddPhaseOfReflection c) (-z) =
          -rawSuzukiW Vplus Vminus (oddPhaseOfReflection c) z := by
  exact ⟨oddPhaseOfReflection_unitPhase hc,
    rawSuzukiW_odd_of_oddPhaseOfReflection Vplus Vminus hreflect
      (unitPhase_ne_zero hc)⟩

/-- Raw even branch after a supplied deficiency reflection. -/
theorem rawSuzukiW_even_of_phase_mul_reflection_eq_neg_one
    (Vplus Vminus : ℂ → ℂ) {phase c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hphase : phase * c = -1) :
    ∀ z : ℂ, rawSuzukiW Vplus Vminus phase (-z) = rawSuzukiW Vplus Vminus phase z := by
  intro z
  rw [rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
  rw [rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
  exact suzukiW_even_of_phase_mul_reflection_eq_neg_one Vplus hphase z

/-- Raw even branch for the selected reflection phase. -/
theorem rawSuzukiW_even_of_evenPhaseOfReflection
    (Vplus Vminus : ℂ → ℂ) {c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : c ≠ 0) :
    ∀ z : ℂ,
      rawSuzukiW Vplus Vminus (evenPhaseOfReflection c) (-z) =
        rawSuzukiW Vplus Vminus (evenPhaseOfReflection c) z :=
  rawSuzukiW_even_of_phase_mul_reflection_eq_neg_one Vplus Vminus hreflect
    (evenPhaseOfReflection_mul_reflection_eq_neg_one hc)

/-- A unitary reflection scalar supplies a legal unit-circle even phase and
makes the raw Suzuki boundary expression even. -/
theorem evenPhase_unitPhase_and_rawSuzukiW_even
    (Vplus Vminus : ℂ → ℂ) {c : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : UnitPhase c) :
    UnitPhase (evenPhaseOfReflection c) ∧
      ∀ z : ℂ,
        rawSuzukiW Vplus Vminus (evenPhaseOfReflection c) (-z) =
          rawSuzukiW Vplus Vminus (evenPhaseOfReflection c) z := by
  exact ⟨evenPhaseOfReflection_unitPhase hc,
    rawSuzukiW_even_of_evenPhaseOfReflection Vplus Vminus hreflect
      (unitPhase_ne_zero hc)⟩

/-- Under a nonzero odd probe at `z`, oddness at `z` forces
`phase * c = 1`. -/
theorem phase_mul_reflection_eq_one_of_suzukiW_odd_at
    (V : ℂ → ℂ) {phase c z : ℂ}
    (hodd : suzukiW V phase c (-z) = -suzukiW V phase c z)
    (hprobe : oddProbe V z ≠ 0) :
    phase * c = 1 := by
  have hsum : suzukiW V phase c (-z) + suzukiW V phase c z = 0 := by
    rw [hodd]
    ring
  have hmul : (1 - phase * c) * oddProbe V z = 0 := by
    have hfactor :
        suzukiW V phase c (-z) + suzukiW V phase c z =
          (1 - phase * c) * oddProbe V z := by
      simp [suzukiW, oddProbe]
      ring
    rwa [← hfactor]
  have hleft : 1 - phase * c = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hprobe
  exact (sub_eq_zero.mp hleft).symm

/-- Under a nonzero even probe at `z`, evenness at `z` forces
`phase * c = -1`. -/
theorem phase_mul_reflection_eq_neg_one_of_suzukiW_even_at
    (V : ℂ → ℂ) {phase c z : ℂ}
    (heven : suzukiW V phase c (-z) = suzukiW V phase c z)
    (hprobe : evenProbe V z ≠ 0) :
    phase * c = -1 := by
  have hdiff : suzukiW V phase c (-z) - suzukiW V phase c z = 0 := by
    rw [heven]
    ring
  have hmul : -((1 + phase * c) * evenProbe V z) = 0 := by
    have hfactor :
        suzukiW V phase c (-z) - suzukiW V phase c z =
          -((1 + phase * c) * evenProbe V z) := by
      simp [suzukiW, evenProbe]
      ring
    rwa [← hfactor]
  have hmul' : (1 + phase * c) * evenProbe V z = 0 :=
    neg_eq_zero.mp hmul
  have hleft : 1 + phase * c = 0 :=
    (mul_eq_zero.mp hmul').resolve_right hprobe
  calc
    phase * c = (1 + phase * c) - 1 := by ring
    _ = 0 - 1 := by rw [hleft]
    _ = -1 := by ring

/-- Odd branch uniqueness under a nonzero odd probe. -/
theorem suzukiW_odd_at_iff_phase_mul_reflection_eq_one
    (V : ℂ → ℂ) {phase c z : ℂ}
    (hprobe : oddProbe V z ≠ 0) :
    suzukiW V phase c (-z) = -suzukiW V phase c z ↔ phase * c = 1 := by
  constructor
  · intro hodd
    exact phase_mul_reflection_eq_one_of_suzukiW_odd_at V hodd hprobe
  · intro hphase
    exact suzukiW_odd_of_phase_mul_reflection_eq_one V hphase z

/-- Under a nonzero odd probe and nonzero reflection scalar, oddness at `z`
forces the selected odd-branch phase. -/
theorem phase_eq_oddPhaseOfReflection_of_suzukiW_odd_at
    (V : ℂ → ℂ) {phase c z : ℂ}
    (hc : c ≠ 0)
    (hodd : suzukiW V phase c (-z) = -suzukiW V phase c z)
    (hprobe : oddProbe V z ≠ 0) :
    phase = oddPhaseOfReflection c :=
  phase_eq_oddPhaseOfReflection_of_phase_mul_reflection_eq_one hc
    (phase_mul_reflection_eq_one_of_suzukiW_odd_at V hodd hprobe)

/-- Even branch uniqueness under a nonzero even probe. -/
theorem suzukiW_even_at_iff_phase_mul_reflection_eq_neg_one
    (V : ℂ → ℂ) {phase c z : ℂ}
    (hprobe : evenProbe V z ≠ 0) :
    suzukiW V phase c (-z) = suzukiW V phase c z ↔ phase * c = -1 := by
  constructor
  · intro heven
    exact phase_mul_reflection_eq_neg_one_of_suzukiW_even_at V heven hprobe
  · intro hphase
    exact suzukiW_even_of_phase_mul_reflection_eq_neg_one V hphase z

/-- Under a nonzero even probe and nonzero reflection scalar, evenness at `z`
forces the selected even-branch phase. -/
theorem phase_eq_evenPhaseOfReflection_of_suzukiW_even_at
    (V : ℂ → ℂ) {phase c z : ℂ}
    (hc : c ≠ 0)
    (heven : suzukiW V phase c (-z) = suzukiW V phase c z)
    (hprobe : evenProbe V z ≠ 0) :
    phase = evenPhaseOfReflection c :=
  phase_eq_evenPhaseOfReflection_of_phase_mul_reflection_eq_neg_one hc
    (phase_mul_reflection_eq_neg_one_of_suzukiW_even_at V heven hprobe)

/-- Under a supplied deficiency reflection and nonzero odd probe at `z`, raw
oddness at `z` forces `phase * c = 1`. -/
theorem phase_mul_reflection_eq_one_of_rawSuzukiW_odd_at
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hodd : rawSuzukiW Vplus Vminus phase (-z) = -rawSuzukiW Vplus Vminus phase z)
    (hprobe : oddProbe Vplus z ≠ 0) :
    phase * c = 1 := by
  have hsuz : suzukiW Vplus phase c (-z) = -suzukiW Vplus phase c z := by
    rw [← rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
    rw [← rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
    exact hodd
  exact phase_mul_reflection_eq_one_of_suzukiW_odd_at Vplus hsuz hprobe

/-- Under a supplied deficiency reflection and nonzero even probe at `z`, raw
evenness at `z` forces `phase * c = -1`. -/
theorem phase_mul_reflection_eq_neg_one_of_rawSuzukiW_even_at
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (heven : rawSuzukiW Vplus Vminus phase (-z) = rawSuzukiW Vplus Vminus phase z)
    (hprobe : evenProbe Vplus z ≠ 0) :
    phase * c = -1 := by
  have hsuz : suzukiW Vplus phase c (-z) = suzukiW Vplus phase c z := by
    rw [← rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
    rw [← rawSuzukiW_eq_suzukiW_of_deficiencyReflection Vplus Vminus hreflect]
    exact heven
  exact phase_mul_reflection_eq_neg_one_of_suzukiW_even_at Vplus hsuz hprobe

/-- Raw odd branch uniqueness under a supplied deficiency reflection and
nonzero odd probe. -/
theorem rawSuzukiW_odd_at_iff_phase_mul_reflection_eq_one
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hprobe : oddProbe Vplus z ≠ 0) :
    rawSuzukiW Vplus Vminus phase (-z) = -rawSuzukiW Vplus Vminus phase z ↔ phase * c = 1 := by
  constructor
  · intro hodd
    exact phase_mul_reflection_eq_one_of_rawSuzukiW_odd_at Vplus Vminus hreflect hodd hprobe
  · intro hphase
    exact rawSuzukiW_odd_of_phase_mul_reflection_eq_one Vplus Vminus hreflect hphase z

/-- Raw oddness at a nonzero probe forces the selected odd-branch phase. -/
theorem phase_eq_oddPhaseOfReflection_of_rawSuzukiW_odd_at
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : c ≠ 0)
    (hodd : rawSuzukiW Vplus Vminus phase (-z) = -rawSuzukiW Vplus Vminus phase z)
    (hprobe : oddProbe Vplus z ≠ 0) :
    phase = oddPhaseOfReflection c :=
  phase_eq_oddPhaseOfReflection_of_phase_mul_reflection_eq_one hc
    (phase_mul_reflection_eq_one_of_rawSuzukiW_odd_at
      Vplus Vminus hreflect hodd hprobe)

/-- Raw even branch uniqueness under a supplied deficiency reflection and
nonzero even probe. -/
theorem rawSuzukiW_even_at_iff_phase_mul_reflection_eq_neg_one
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hprobe : evenProbe Vplus z ≠ 0) :
    rawSuzukiW Vplus Vminus phase (-z) = rawSuzukiW Vplus Vminus phase z ↔ phase * c = -1 := by
  constructor
  · intro heven
    exact phase_mul_reflection_eq_neg_one_of_rawSuzukiW_even_at Vplus Vminus hreflect heven hprobe
  · intro hphase
    exact rawSuzukiW_even_of_phase_mul_reflection_eq_neg_one Vplus Vminus hreflect hphase z

/-- Raw evenness at a nonzero probe forces the selected even-branch phase. -/
theorem phase_eq_evenPhaseOfReflection_of_rawSuzukiW_even_at
    (Vplus Vminus : ℂ → ℂ) {phase c z : ℂ}
    (hreflect : DeficiencyReflection Vplus Vminus c)
    (hc : c ≠ 0)
    (heven : rawSuzukiW Vplus Vminus phase (-z) = rawSuzukiW Vplus Vminus phase z)
    (hprobe : evenProbe Vplus z ≠ 0) :
    phase = evenPhaseOfReflection c :=
  phase_eq_evenPhaseOfReflection_of_phase_mul_reflection_eq_neg_one hc
    (phase_mul_reflection_eq_neg_one_of_rawSuzukiW_even_at
      Vplus Vminus hreflect heven hprobe)

/-- A complex-valued function is even when it is invariant under `z ↦ -z`. -/
def EvenFunction (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F (-z) = F z

/-- A complex-valued function is odd when it changes sign under `z ↦ -z`. -/
def OddFunction (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F (-z) = -F z

/-- Pointwise limits of odd complex-valued functions remain odd.

This is only a pointwise filtered-limit parity statement; it does not assert
uniform convergence, holomorphy, or any Suzuki limiting theorem. -/
theorem oddFunction_of_tendsto_odd
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {Fs : ι → ℂ → ℂ} {F : ℂ → ℂ}
    (hodd : ∀ i : ι, OddFunction (Fs i))
    (hlim : ∀ z : ℂ, Filter.Tendsto (fun i : ι => Fs i z) l (nhds (F z))) :
    OddFunction F := by
  intro z
  have hfun : (fun i : ι => Fs i (-z)) = fun i : ι => -Fs i z := by
    funext i
    exact hodd i z
  have hlim_neg : Filter.Tendsto (fun i : ι => -Fs i z) l (nhds (F (-z))) := by
    simpa [hfun] using hlim (-z)
  exact tendsto_nhds_unique hlim_neg ((hlim z).neg)

/-- Pointwise limits of even complex-valued functions remain even.

This is only a pointwise filtered-limit parity statement; it does not assert
uniform convergence, holomorphy, or any Suzuki limiting theorem. -/
theorem evenFunction_of_tendsto_even
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {Fs : ι → ℂ → ℂ} {F : ℂ → ℂ}
    (heven : ∀ i : ι, EvenFunction (Fs i))
    (hlim : ∀ z : ℂ, Filter.Tendsto (fun i : ι => Fs i z) l (nhds (F z))) :
    EvenFunction F := by
  intro z
  have hfun : (fun i : ι => Fs i (-z)) = fun i : ι => Fs i z := by
    funext i
    exact heven i z
  have hlim_neg : Filter.Tendsto (fun i : ι => Fs i z) l (nhds (F (-z))) := by
    simpa [hfun] using hlim (-z)
  exact tendsto_nhds_unique hlim_neg (hlim z)

/-- If each raw Suzuki boundary expression is on the odd phase branch and the
expressions converge pointwise, then the pointwise limit is odd.

The convergence hypothesis is external.  This theorem does not prove Suzuki's
convergence corollary, the deficiency-reflection identity, a canonical phase, or
RH. -/
theorem oddFunction_of_tendsto_rawSuzukiW_phase_mul_reflection_eq_one
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {Vplus Vminus : ι → ℂ → ℂ} {phase c : ι → ℂ} {F : ℂ → ℂ}
    (hreflect : ∀ i : ι, DeficiencyReflection (Vplus i) (Vminus i) (c i))
    (hphase : ∀ i : ι, phase i * c i = 1)
    (hlim : ∀ z : ℂ,
      Filter.Tendsto
        (fun i : ι => rawSuzukiW (Vplus i) (Vminus i) (phase i) z)
        l (nhds (F z))) :
    OddFunction F := by
  exact oddFunction_of_tendsto_odd
    (fun i => rawSuzukiW_odd_of_phase_mul_reflection_eq_one
      (Vplus i) (Vminus i) (hreflect i) (hphase i))
    hlim

/-- Multiplying an odd function by an even one preserves oddness. -/
theorem oddFunction_mul_even_odd
    {E O : ℂ → ℂ}
    (hE : EvenFunction E)
    (hO : OddFunction O) :
    OddFunction (fun z : ℂ => E z * O z) := by
  intro z
  simp [hE z, hO z]

/-- If the normalizing factors are even, each raw Suzuki boundary expression is
on the odd phase branch, and the normalized expressions converge pointwise, then
the pointwise limit is odd.

This matches the parity bookkeeping for Suzuki's optional `exp(phi(a,z))`
normalizer.  The convergence hypothesis and evenness of the normalizer are
external; this theorem does not prove Suzuki's convergence corollary or RH. -/
theorem oddFunction_of_tendsto_even_mul_rawSuzukiW_phase_mul_reflection_eq_one
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {normalizer : ι → ℂ → ℂ} {Vplus Vminus : ι → ℂ → ℂ}
    {phase c : ι → ℂ} {F : ℂ → ℂ}
    (hnormalizer : ∀ i : ι, EvenFunction (normalizer i))
    (hreflect : ∀ i : ι, DeficiencyReflection (Vplus i) (Vminus i) (c i))
    (hphase : ∀ i : ι, phase i * c i = 1)
    (hlim : ∀ z : ℂ,
      Filter.Tendsto
        (fun i : ι => normalizer i z * rawSuzukiW (Vplus i) (Vminus i) (phase i) z)
        l (nhds (F z))) :
    OddFunction F := by
  exact oddFunction_of_tendsto_odd
    (fun i => oddFunction_mul_even_odd (hnormalizer i)
      (rawSuzukiW_odd_of_phase_mul_reflection_eq_one
        (Vplus i) (Vminus i) (hreflect i) (hphase i)))
    hlim

/-- Pull an abstract completed function back to the critical-line coordinate
`s = 1/2 - i z`. -/
noncomputable def criticalLinePullback (Xi : ℂ → ℂ) (z : ℂ) : ℂ :=
  Xi ((1 : ℂ) / 2 - Complex.I * z)

/-- Pull an abstract `s`-variable derivative back to the critical-line
coordinate.  This is not `deriv (criticalLinePullback Xi)`; the two differ by
the chain-rule scalar when `Xi'` is a derivative of `Xi`. -/
noncomputable def criticalLineSDerivativePullback (Xi' : ℂ → ℂ) (z : ℂ) : ℂ :=
  Xi' ((1 : ℂ) / 2 - Complex.I * z)

/-- A functional equation `Xi(1 - s) = Xi(s)` makes the critical-line
pullback even in the height coordinate. -/
theorem criticalLinePullback_even_of_functionalEquation
    {Xi : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi (1 - s) = Xi s) :
    EvenFunction (criticalLinePullback Xi) := by
  intro z
  have h := hXi ((1 : ℂ) / 2 - Complex.I * z)
  have harg :
      1 - ((1 : ℂ) / 2 - Complex.I * z) =
        (1 : ℂ) / 2 + Complex.I * z := by
    ring
  rw [harg] at h
  simpa [criticalLinePullback] using h

/-- Abstract calculus parity bridge: any derivative witness for an even
complex function is odd. -/
theorem derivative_odd_of_even
    {F F' : ℂ → ℂ}
    (hF : EvenFunction F)
    (hderiv : ∀ z : ℂ, HasDerivAt F (F' z) z) :
    OddFunction F' := by
  intro z
  have hleft : HasDerivAt (fun w : ℂ => F (-w)) (-(F' (-z))) z := by
    simpa [mul_comm] using (hderiv (-z)).comp z (hasDerivAt_neg z)
  have heq : (fun w : ℂ => F (-w)) = F := by
    funext w
    exact hF w
  rw [heq] at hleft
  have huniq : -(F' (-z)) = F' z := hleft.unique (hderiv z)
  calc
    F' (-z) = -(-(F' (-z))) := by ring
    _ = -F' z := by rw [huniq]

/-- Version of `derivative_odd_of_even` for mathlib's `deriv`. -/
theorem deriv_odd_of_even
    {F : ℂ → ℂ}
    (hF : EvenFunction F)
    (hderiv : Differentiable ℂ F) :
    OddFunction (deriv F) := by
  exact derivative_odd_of_even hF fun z => (hderiv z).hasDerivAt

/-- Differentiating the abstract functional equation `Xi(1 - s) = Xi(s)`:
any global derivative witness for `Xi` is odd under the reflection `s ↦ 1-s`.
-/
theorem derivative_reflects_neg_of_functionalEquation
    {Xi Xi' : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi (1 - s) = Xi s)
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s) :
    ∀ s : ℂ, Xi' (1 - s) = -Xi' s := by
  intro s
  have hleft : HasDerivAt (fun t : ℂ => Xi (1 - t)) (-(Xi' (1 - s))) s := by
    simpa using (hderiv (1 - s)).comp_const_sub (1 : ℂ) s
  have heq : (fun t : ℂ => Xi (1 - t)) = Xi := by
    funext t
    exact hXi t
  rw [heq] at hleft
  have huniq : -(Xi' (1 - s)) = Xi' s := hleft.unique (hderiv s)
  calc
    Xi' (1 - s) = -(-(Xi' (1 - s))) := by ring
    _ = -Xi' s := by rw [huniq]

/-- The critical-line pullback of an `s`-variable derivative witness is odd. -/
theorem criticalLineSDerivativePullback_odd_of_functionalEquation
    {Xi Xi' : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi (1 - s) = Xi s)
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s) :
    OddFunction (criticalLineSDerivativePullback Xi') := by
  intro z
  have h :=
    derivative_reflects_neg_of_functionalEquation hXi hderiv
      ((1 : ℂ) / 2 - Complex.I * z)
  have harg :
      1 - ((1 : ℂ) / 2 - Complex.I * z) =
        (1 : ℂ) / 2 + Complex.I * z := by
    ring
  rw [harg] at h
  simpa [criticalLineSDerivativePullback] using h

/-- Chain-rule bridge between the critical-line pullback derivative and the
pulled-back `s`-variable derivative. -/
theorem criticalLinePullback_hasDerivAt_sDerivative
    {Xi Xi' : ℂ → ℂ}
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s)
    (z : ℂ) :
    HasDerivAt (criticalLinePullback Xi)
      (-Complex.I * criticalLineSDerivativePullback Xi' z) z := by
  change HasDerivAt (fun w : ℂ => Xi ((1 : ℂ) / 2 - Complex.I * w))
      (-Complex.I * Xi' ((1 : ℂ) / 2 - Complex.I * z)) z
  have hinner : HasDerivAt (fun w : ℂ => (1 : ℂ) / 2 - Complex.I * w) (-Complex.I) z := by
    simpa using ((hasDerivAt_id z).const_mul Complex.I).const_sub ((1 : ℂ) / 2)
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc]
    using (hderiv ((1 : ℂ) / 2 - Complex.I * z)).comp z hinner

/-- `deriv` form of `criticalLinePullback_hasDerivAt_sDerivative`. -/
theorem deriv_criticalLinePullback_eq_sDerivative
    {Xi Xi' : ℂ → ℂ}
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s)
    (z : ℂ) :
    deriv (criticalLinePullback Xi) z =
      -Complex.I * criticalLineSDerivativePullback Xi' z :=
  (criticalLinePullback_hasDerivAt_sDerivative hderiv z).deriv

/-- Abstract form of Suzuki's limiting quotient:
`z^2 * numerator(z) / denominator(z)`.

This is only the algebraic expression whose parity is checked below; no
analytic regularity or nonvanishing assertion is bundled into this definition. -/
noncomputable def limitQuotient (numerator denominator : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ 2 * numerator z / denominator z

/-- Algebraic relation between the two denominator conventions for the
critical-line quotient.  Since Lean's field division is total, this is only an
identity of field-valued expressions; it does not assert denominator
nonvanishing or holomorphic quotient behavior at zeros. -/
theorem limitQuotient_pullback_deriv_eq_I_sDerivative
    {Xi Xi' : ℂ → ℂ}
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s)
    (z : ℂ) :
    limitQuotient (criticalLinePullback Xi) (deriv (criticalLinePullback Xi)) z =
      Complex.I * limitQuotient (criticalLinePullback Xi) (criticalLineSDerivativePullback Xi') z := by
  simp [limitQuotient]
  rw [deriv_criticalLinePullback_eq_sDerivative hderiv z]
  simp [div_eq_mul_inv, Complex.inv_I]
  ring

/-- Suzuki limiting-target parity: an even numerator and odd denominator make
`z^2 * numerator / denominator` odd. -/
theorem limitQuotient_odd_of_even_numerator_odd_denominator
    {numerator denominator : ℂ → ℂ}
    (hnum : EvenFunction numerator)
    (hden : OddFunction denominator) :
    OddFunction (limitQuotient numerator denominator) := by
  intro z
  simp [limitQuotient, hnum z, hden z]
  ring

/-- Abstract Suzuki target parity from only functional-equation symmetry:
`F(z) = Xi(1/2 - i z)` is even, so `z^2 * F(z) / F'(z)` is odd.

This theorem uses the derivative of the pulled-back function.  It does not
identify that derivative with a separately defined derivative of `Xi` in the
`s` variable. -/
theorem criticalLinePullback_limitQuotient_odd_of_functionalEquation
    {Xi : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi (1 - s) = Xi s)
    (hderiv : Differentiable ℂ (criticalLinePullback Xi)) :
    OddFunction
      (limitQuotient (criticalLinePullback Xi) (deriv (criticalLinePullback Xi))) := by
  have hpull : EvenFunction (criticalLinePullback Xi) :=
    criticalLinePullback_even_of_functionalEquation hXi
  exact limitQuotient_odd_of_even_numerator_odd_denominator hpull
    (deriv_odd_of_even hpull hderiv)

/-- Abstract Suzuki target parity using an `s`-variable derivative denominator:
if `Xi(1-s)=Xi(s)` and `Xi'` is a derivative witness for `Xi`, then
`z^2 * Xi(1/2 - i z) / Xi'(1/2 - i z)` is odd.

This is only a parity statement for the field-valued quotient.  It does not
assert nonvanishing, holomorphy, convergence, or that a concrete `xi` satisfies
the hypotheses. -/
theorem criticalLinePullback_limitQuotient_odd_of_functionalEquation_sDerivative
    {Xi Xi' : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi (1 - s) = Xi s)
    (hderiv : ∀ s : ℂ, HasDerivAt Xi (Xi' s) s) :
    OddFunction
      (limitQuotient (criticalLinePullback Xi) (criticalLineSDerivativePullback Xi')) := by
  exact limitQuotient_odd_of_even_numerator_odd_denominator
    (criticalLinePullback_even_of_functionalEquation hXi)
    (criticalLineSDerivativePullback_odd_of_functionalEquation hXi hderiv)

end SuzukiPhase
end JensenLadder
