import JensenLadder.ArithmeticSiteCarrier
import JensenLadder.PrimitiveHodgeWeilEngine

/-!
# Primitive Hodge--Weil calibration

This module calibrates the abstract primitive Hodge--Riemann interface.

`PrimitiveHodgeWeilEngine` records the algebraic handoff

```text
  Q_W(v) = - <P(v), P(v)>,    P(v) primitive,
  <X, X> <= 0 on primitives.
```

That handoff is useful only when the sign theorem comes from an external
arithmetic source.  With a completely abstract `Engine`, the handoff is exactly
as strong as the target positive-semidefinite row: any already-PSD finite Weil
form admits a tautological primitive realization.

This is the Lean-facing version of the corrected geometric-positivity rule:
finite primitive/Lefschetz signatures are diagnostics unless they are backed by
an arithmetic Hodge-index/Deninger carrier.  This file does not construct that
carrier, a matroid, a Chow ring, a trace formula, or an RH proof.

Evidence class: dead-end elimination / formal certificate.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace PrimitiveHodgeWeilCalibration

open CCMFiniteWeil
open HodgeWeilBridge
open PrimitiveHodgeWeilEngine

universe u v w

variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

/--
The tautological primitive engine attached to an already positive semidefinite
finite Weil form.

This construction is deliberately circular as a proof method: the primitive
sign row is just the assumed target PSD row rewritten as a self-intersection
inequality.
-/
noncomputable def tautologicalEngine
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (hpsd : TargetSharpPositivity D) :
    Engine.{v} where
  ChowClass := ι -> ℝ
  intersectionForm := fun X _Y => -quadraticForm D X
  lefschetzClass := fun _ => 0
  primitive := fun _ => True
  primitive_nonpos := by
    intro X _hX
    exact neg_nonpos.mpr (hpsd X)

/--
The tautological primitive realization of an already PSD finite Weil form.

The projection is the identity on finite vectors, and the "intersection form"
was defined precisely so that `Q_W(v) = -<v,v>`.
-/
noncomputable def tautologicalPrimitiveWeilRealization
    (D : SemilocalFiniteWeilData ι κ ℝ)
    (hpsd : TargetSharpPositivity D) :
    PrimitiveWeilRealization.{v} D where
  engine := tautologicalEngine D hpsd
  primitiveProjection := id
  primitive_projection := by
    intro _v
    trivial
  quadratic_eq_neg_primitive_intersection := by
    intro v
    simp [tautologicalEngine]

/--
Target-sharp PSD supplies an abstract engine-backed realization.

This is a calibration theorem, not a proof route: it shows that the abstract
engine interface has no proof content unless the engine is supplied by an
external arithmetic construction.
-/
theorem engineBackedPositivity_of_targetSharpPositivity
    {D : SemilocalFiniteWeilData ι κ ℝ}
    (hpsd : TargetSharpPositivity D) :
    EngineBackedPositivity.{v} D :=
  ⟨tautologicalPrimitiveWeilRealization D hpsd⟩

/--
At the finite abstract-interface level, engine-backed positivity is exactly
target-sharp positive semidefiniteness.

The forward direction is the genuine Hodge handoff.  The reverse direction is
the tautological relabeling above, and records why an external arithmetic
source is the missing object.
-/
theorem engineBackedPositivity_iff_targetSharpPositivity
    (D : SemilocalFiniteWeilData ι κ ℝ) :
    EngineBackedPositivity.{v} D ↔ TargetSharpPositivity D := by
  constructor
  · exact targetSharpPositivity_of_engineBacked
  · exact engineBackedPositivity_of_targetSharpPositivity

/--
An arithmetic-backed primitive certificate packages both sides of the corrected
rule: a Deninger/arithmetic-site carrier supplying external rows, and a finite
primitive realization of a semilocal Weil form.

The finite realization gives finite PSD.  The arithmetic faithful rows are the
non-finite external carrier rows that prove RH through `ArithmeticSiteCarrier`.
-/
structure ArithmeticBackedPrimitiveCertificate where
  arithmeticCarrier : ArithmeticSiteCarrier.Carrier.{u}
  faithfulRows : arithmeticCarrier.FaithfulRows
  data : SemilocalFiniteWeilData ι κ ℝ
  primitiveRealization : PrimitiveWeilRealization.{v} data

namespace ArithmeticBackedPrimitiveCertificate

/-- The finite primitive realization supplies target-sharp PSD for the packaged
semilocal Weil form. -/
theorem targetSharpPositivity
    (C : ArithmeticBackedPrimitiveCertificate.{u, v, w}
      (ι := ι) (κ := κ)) :
    TargetSharpPositivity C.data :=
  C.primitiveRealization.positiveSemidefinite

/-- The finite primitive realization supplies pointwise nonnegativity. -/
theorem quadraticForm_nonnegative
    (C : ArithmeticBackedPrimitiveCertificate.{u, v, w}
      (ι := ι) (κ := κ))
    (x : ι -> ℝ) :
    0 ≤ quadraticForm C.data x :=
  C.primitiveRealization.quadraticForm_nonnegative x

/--
The arithmetic faithful rows, not the finite diagnostic alone, are what prove
mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis
    (C : ArithmeticBackedPrimitiveCertificate.{u, v, w}
      (ι := ι) (κ := κ)) :
    RiemannHypothesis :=
  ArithmeticSiteCarrier.riemannHypothesis_of_faithfulRows
    C.arithmeticCarrier C.faithfulRows

/-- The arithmetic rows also supply the existing Deninger faithful dictionary. -/
theorem hasPolarizedFaithfulDictionary
    (C : ArithmeticBackedPrimitiveCertificate.{u, v, w}
      (ι := ι) (κ := κ)) :
    DeningerCarrier.HasPolarizedFaithfulDictionary.{u} :=
  ⟨C.arithmeticCarrier.spectralCarrier,
    ArithmeticSiteCarrier.polarizedFaithfulDictionary_of_faithfulRows
      C.arithmeticCarrier C.faithfulRows⟩

end ArithmeticBackedPrimitiveCertificate

end PrimitiveHodgeWeilCalibration
end JensenLadder
