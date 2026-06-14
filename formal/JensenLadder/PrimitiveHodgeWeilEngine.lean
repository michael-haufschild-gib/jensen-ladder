import JensenLadder.HodgeWeilBridge

/-!
# Primitive Hodge--Riemann engine for finite Weil forms

The geometric positivity rule says that RH-relevant positivity must come from
an external arithmetic theorem, such as an arithmetic Hodge index package,
rather than from a positivity statement equivalent to RH.

This module records the finite algebraic shape of that rule.  A finite Weil
quadratic form is engine-backed when it factors through the primitive part of a
Deninger-style arithmetic Hodge-index / polarized cohomology engine:

```text
  Q_W(v) = - <P(v), P(v)>,     P(v) primitive,
  <X, X> <= 0 on primitives.
```

Then `Q_W` is positive semidefinite.  This is the finite primitive/Lefschetz
version of the existing `HodgeWeilBridge`.

This file does not construct Deninger cohomology, an arithmetic surface,
Lefschetz operator, trace formula, or RH proof.  It also should not be read as a
combinatorial/matroid shortcut.  It only formalizes the engine handoff that a
genuine arithmetic construction must instantiate.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace PrimitiveHodgeWeilEngine

open HodgeWeilBridge
open CCMFiniteWeil

universe u

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/--
A finite Hodge--Riemann positivity engine.

`ChowClass` is intentionally abstract: it is meant as a placeholder for a
genuine arithmetic cohomology/intersection group, or another externally
constructed arithmetic structure with the same Lefschetz/primitive theorem. The
load-bearing field is
`primitive_nonpos`, the external Hodge--Riemann sign theorem on primitive
classes.
-/
structure Engine where
  ChowClass : Type u
  intersectionForm : ChowClass -> ChowClass -> ℝ
  lefschetzClass : ChowClass
  primitive : ChowClass -> Prop
  primitive_nonpos :
    ∀ X : ChowClass, primitive X -> intersectionForm X X ≤ 0

/--
Primitive/Lefschetz realization of a finite semilocal Weil form.

The map `primitiveProjection` is the finite analogue of taking the primitive
part of a class.  The crucial trace/realization row is
`quadratic_eq_neg_primitive_intersection`: the Weil quadratic form must be the
negative self-intersection of that primitive part.
-/
structure PrimitiveWeilRealization
    (D : SemilocalFiniteWeilData ι κ ℝ) where
  engine : Engine.{u}
  primitiveProjection : (ι -> ℝ) -> engine.ChowClass
  primitive_projection :
    ∀ v : ι -> ℝ, engine.primitive (primitiveProjection v)
  quadratic_eq_neg_primitive_intersection :
    ∀ v : ι -> ℝ,
      HodgeWeilBridge.quadraticForm D v =
        -engine.intersectionForm (primitiveProjection v) (primitiveProjection v)

namespace PrimitiveWeilRealization

variable {D : SemilocalFiniteWeilData ι κ ℝ}

/-- The primitive projection has nonpositive self-intersection. -/
theorem primitiveProjection_selfIntersection_nonpos
    (H : PrimitiveWeilRealization.{u} D)
    (v : ι -> ℝ) :
    H.engine.intersectionForm (H.primitiveProjection v) (H.primitiveProjection v) ≤ 0 :=
  H.engine.primitive_nonpos (H.primitiveProjection v) (H.primitive_projection v)

/-- The finite Weil quadratic form is nonnegative when it is backed by a
primitive Hodge--Riemann engine. -/
theorem quadraticForm_nonnegative
    (H : PrimitiveWeilRealization.{u} D)
    (v : ι -> ℝ) :
    0 ≤ HodgeWeilBridge.quadraticForm D v := by
  rw [H.quadratic_eq_neg_primitive_intersection v]
  linarith [H.primitiveProjection_selfIntersection_nonpos v]

/-- A primitive Hodge--Riemann realization supplies PSD of the finite Weil form. -/
theorem positiveSemidefinite
    (H : PrimitiveWeilRealization.{u} D) :
    HodgeWeilBridge.PositiveSemidefinite D := by
  intro v
  exact H.quadraticForm_nonnegative v

/--
Forget the Lefschetz language: a primitive Hodge--Riemann realization is an
ordinary finite Hodge realization for the existing bridge.
-/
def toFiniteHodgeRealization
    (H : PrimitiveWeilRealization.{u} D) :
    HodgeWeilBridge.FiniteHodgeRealization.{u} D where
  DivisorClass := H.engine.ChowClass
  intersectionForm := H.engine.intersectionForm
  primitive := H.engine.primitive
  realize := H.primitiveProjection
  primitive_realize := H.primitive_projection
  hodgeIndex_nonpos := H.engine.primitive_nonpos
  quadratic_eq_neg_intersection :=
    H.quadratic_eq_neg_primitive_intersection

/-- A negative vector contradicts a primitive Hodge--Riemann realization. -/
theorem false_of_negative_quadraticForm
    (H : PrimitiveWeilRealization.{u} D)
    {v : ι -> ℝ}
    (hv : HodgeWeilBridge.quadraticForm D v < 0) :
    False :=
  HodgeWeilBridge.not_positiveSemidefinite_of_negative_quadraticForm hv
    H.positiveSemidefinite

end PrimitiveWeilRealization

/--
Target-sharp positivity is merely the PSD statement for the finite Weil form.
It is a target row unless backed by an external Hodge--Riemann engine.
-/
def TargetSharpPositivity
    (D : SemilocalFiniteWeilData ι κ ℝ) : Prop :=
  HodgeWeilBridge.PositiveSemidefinite D

/-- Engine-backed positivity: the finite Weil form is realized through a
primitive Hodge--Riemann engine. -/
def EngineBackedPositivity
    (D : SemilocalFiniteWeilData ι κ ℝ) : Prop :=
  Nonempty (PrimitiveWeilRealization.{u} D)

/-- Engine-backed positivity supplies the target-sharp PSD row. -/
theorem targetSharpPositivity_of_engineBacked
    {D : SemilocalFiniteWeilData ι κ ℝ}
    (h : EngineBackedPositivity.{u} D) :
    TargetSharpPositivity D := by
  rcases h with ⟨H⟩
  exact H.positiveSemidefinite

/-- A negative vector rules out engine-backed positivity. -/
theorem not_engineBacked_of_negative_quadraticForm
    {D : SemilocalFiniteWeilData ι κ ℝ} {v : ι -> ℝ}
    (hv : HodgeWeilBridge.quadraticForm D v < 0) :
    ¬ EngineBackedPositivity.{u} D := by
  rintro ⟨H⟩
  exact H.false_of_negative_quadraticForm hv

/-- Any negative vector rules out engine-backed positivity. -/
theorem not_engineBacked_of_hasNegativeVector
    {D : SemilocalFiniteWeilData ι κ ℝ}
    (hneg : HodgeWeilBridge.HasNegativeVector D) :
    ¬ EngineBackedPositivity.{u} D := by
  rcases hneg with ⟨v, hv⟩
  exact not_engineBacked_of_negative_quadraticForm hv

/-- Packaged finite certificate for a primitive Hodge--Riemann engine realizing
a semilocal Weil form. -/
structure PrimitiveHodgeWeilCertificate where
  data : SemilocalFiniteWeilData ι κ ℝ
  realization : PrimitiveWeilRealization.{u} data

namespace PrimitiveHodgeWeilCertificate

/-- The packaged primitive engine supplies target-sharp positivity. -/
theorem targetSharpPositivity
    (C : PrimitiveHodgeWeilCertificate.{u} (ι := ι) (κ := κ)) :
    TargetSharpPositivity C.data :=
  C.realization.positiveSemidefinite

/-- The packaged primitive engine supplies pointwise nonnegativity. -/
theorem quadraticForm_nonnegative
    (C : PrimitiveHodgeWeilCertificate.{u} (ι := ι) (κ := κ))
    (v : ι -> ℝ) :
    0 ≤ HodgeWeilBridge.quadraticForm C.data v :=
  C.realization.quadraticForm_nonnegative v

/-- The packaged primitive engine can be consumed by the older finite Hodge
bridge. -/
def toFiniteHodgeWeilCertificate
    (C : PrimitiveHodgeWeilCertificate.{u} (ι := ι) (κ := κ)) :
    HodgeWeilBridge.FiniteHodgeWeilCertificate.{u} (ι := ι) (κ := κ) where
  data := C.data
  hodgeRealization := C.realization.toFiniteHodgeRealization

end PrimitiveHodgeWeilCertificate

end PrimitiveHodgeWeilEngine
end JensenLadder
