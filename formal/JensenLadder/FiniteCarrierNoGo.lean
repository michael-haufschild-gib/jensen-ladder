import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite exact carrier no-go

This module records the finite-rank obstruction to a literal
finite-dimensional exact carrier for the full `Xi` zero set.

The analytic input that `Xi` has infinitely many zeros is not formalized here.
In paper form it comes from the Riemann--von Mangoldt zero-counting theorem.
The Lean theorem below is the reusable finite combinatorial core: an exact
finite spectral dictionary with only `n` spectral slots cannot faithfully and
separately represent `n + 1` distinct zero labels, and therefore cannot
represent an infinite zero-label type.

The word "label" is intentional.  Multiplicities are represented by distinct
labels even when the underlying zero location is repeated.  This matches the
finite-dimensional characteristic-polynomial obstruction: eigenvalues and zeros
are counted with algebraic multiplicity.

This file does not prove Riemann--von Mangoldt, prove RH, or refute RH.  It
only rules out the literal finite-dimensional exact-carrier theorem.  Viable
carrier statements must use finite truncations with a limiting theorem, an
inverse/direct limit, or an infinite-dimensional Deninger/Connes-style object.

Evidence class: formal/certificate artifact + falsifier for finite exact
carrier statements.  Theorem M is proven, but Theorem M does not prove RH by
itself.
-/

namespace JensenLadder
namespace FiniteCarrierNoGo

universe u

/--
There is no injection from `n + 1` labels into only `n` slots.

This is the pigeonhole principle in the exact form needed for finite spectral
carriers: `n` spectral slots cannot faithfully distinguish `n + 1` zero labels.
-/
theorem not_injective_fin_succ_to_fin
    (n : ℕ) (f : Fin (n + 1) -> Fin n) :
    ¬ Function.Injective f := by
  intro hf
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard
  exact Nat.not_succ_le_self n hcard

/--
A finite exact spectral dictionary with `n` spectral slots.

* `Zero` is a type of zero labels, not necessarily zero locations;
* `represents z γ` says spectral slot `γ` represents zero label `z`;
* `complete` says every zero label is represented;
* `separates` says one spectral slot cannot represent two distinct zero labels.

For a finite-dimensional operator this abstracts the fact that the
characteristic polynomial has only finitely many roots counted with algebraic
multiplicity.  This module avoids formalizing that linear-algebra layer because
the cardinal obstruction is already the load-bearing point.
-/
structure FiniteSpectrumDictionary (n : ℕ) where
  Zero : Type u
  represents : Zero -> Fin n -> Prop
  complete : ∀ z : Zero, ∃ γ : Fin n, represents z γ
  separates :
    ∀ {z w : Zero} {γ : Fin n}, represents z γ -> represents w γ -> z = w

namespace FiniteSpectrumDictionary

/-- Choose a representing spectral slot for a zero label. -/
noncomputable def slot
    {n : ℕ} (D : FiniteSpectrumDictionary.{u} n) (z : D.Zero) : Fin n :=
  Classical.choose (D.complete z)

/-- The chosen slot really represents the zero label. -/
theorem slot_represents
    {n : ℕ} (D : FiniteSpectrumDictionary.{u} n) (z : D.Zero) :
    D.represents z (D.slot z) :=
  Classical.choose_spec (D.complete z)

/--
An exact finite dictionary with `n` slots cannot represent an injected sample
of `n + 1` distinct zero labels.
-/
theorem not_has_more_distinct_zeros_than_slots
    {n : ℕ} (D : FiniteSpectrumDictionary.{u} n)
    (sample : Fin (n + 1) -> D.Zero)
    (hsample : Function.Injective sample) :
    False := by
  let f : Fin (n + 1) -> Fin n := fun i => D.slot (sample i)
  have hf : Function.Injective f := by
    intro i j hij
    apply hsample
    have hi : D.represents (sample i) (f i) := by
      simpa [f] using D.slot_represents (sample i)
    have hj : D.represents (sample j) (f i) := by
      have hj0 : D.represents (sample j) (f j) := by
        simpa [f] using D.slot_represents (sample j)
      rw [hij]
      exact hj0
    exact D.separates hi hj
  exact not_injective_fin_succ_to_fin n f hf

/--
An exact finite dictionary cannot represent an infinite zero-label type.

For `Xi`, the external analytic input is Riemann--von Mangoldt, which supplies
infinitely many zero labels.  Once that input is available, this theorem rules
out a literal finite exact carrier immediately.
-/
theorem not_of_infinite_zero_labels
    {n : ℕ} (D : FiniteSpectrumDictionary.{u} n)
    [Infinite D.Zero] :
    False := by
  let f : D.Zero -> Fin n := fun z => D.slot z
  have hf : Function.Injective f := by
    intro z w hzw
    have hz : D.represents z (f z) := by
      simpa [f] using D.slot_represents z
    have hw : D.represents w (f z) := by
      have hw0 : D.represents w (f w) := by
        simpa [f] using D.slot_represents w
      rw [hzw]
      exact hw0
    exact D.separates hz hw
  exact not_injective_infinite_finite f hf

end FiniteSpectrumDictionary

end FiniteCarrierNoGo
end JensenLadder
