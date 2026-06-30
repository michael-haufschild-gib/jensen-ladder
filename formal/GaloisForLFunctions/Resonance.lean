import GaloisForLFunctions.Core

/-!
# Finite-support resonance bookkeeping

This file formalizes the finite algebra behind the corrected two-column
resonance dictionary in `docs/drafts/multi-q-difference-galois-foundations.md`
§9-10.

It deliberately does not define a function ring, constants, torus dynamics, or a
Picard-Vessiot category. The ledger here is only the finite-support distinction:

* coordinate resonance: every coordinate weight is individually killed;
* diagonal resonance: only the finite sum of coordinate weights vanishes.

The second condition can hold by cancellation even when the first fails. For the
arithmetic prime-log specialization, the diagonal resonance lattice is trivial by
the existing unique-factorization theorem.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Per-coordinate resonance: each coordinate weight vanishes separately. -/
def coordinateResonant {ι A : Type*} [AddCommGroup A]
    (ω : ι → A) (m : ι →₀ ℤ) : Prop :=
  ∀ i, m i • ω i = 0

/-- Diagonal resonance: only the finite total weight vanishes. -/
def diagonalResonant {ι A : Type*} [AddCommGroup A]
    (ω : ι → A) (m : ι →₀ ℤ) : Prop :=
  m.sum (fun i z => z • ω i) = 0

/-- Coordinate resonance implies diagonal resonance. The converse is false in
general, because diagonal resonance may occur by cancellation. -/
theorem diagonalResonant_of_coordinateResonant {ι A : Type*} [AddCommGroup A]
    {ω : ι → A} {m : ι →₀ ℤ} :
    coordinateResonant ω m → diagonalResonant ω m := by
  intro h
  unfold diagonalResonant
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun i _ => h i

/-- If no coordinate has integer torsion, then the coordinate-resonance lattice
is trivial. -/
theorem coordinateResonant_eq_zero_of_no_coordinate_torsion {ι A : Type*} [AddCommGroup A]
    {ω : ι → A} {m : ι →₀ ℤ}
    (hω : ∀ i (n : ℤ), n • ω i = 0 → n = 0) :
    coordinateResonant ω m → m = 0 := by
  intro h
  ext i
  exact hω i (m i) (h i)

/-- Prime-log diagonal resonances are trivial by unique factorization. -/
theorem logPrime_diagonalResonant_eq_zero {m : Nat.Primes →₀ ℤ}
    (h : diagonalResonant (fun p : Nat.Primes => Real.log (p : ℕ)) m) :
    m = 0 := by
  unfold diagonalResonant at h
  apply log_prime_int_relation_eq_zero
  rw [← h]
  refine Finsupp.sum_congr ?_
  intro p _
  rw [zsmul_eq_mul]

/-- Frequencies with a visible two-term cancellation. -/
def pairCancelFrequencies : Fin 2 → ℤ :=
  fun i => if i = (0 : Fin 2) then 1 else -1

/-- The relation `(1,1)` on the two cancellation frequencies. -/
def pairCancelRelation : Fin 2 →₀ ℤ :=
  Finsupp.single (0 : Fin 2) (1 : ℤ) + Finsupp.single (1 : Fin 2) (1 : ℤ)

/-- The pair-cancellation relation is diagonally resonant. -/
theorem pairCancel_diagonalResonant :
    diagonalResonant pairCancelFrequencies pairCancelRelation := by
  unfold diagonalResonant pairCancelRelation
  rw [Finsupp.sum_add_index]
  · simp [pairCancelFrequencies]
  · intro i
    simp
  · intro i _ b c
    simp [add_mul]

/-- The same pair-cancellation relation is not coordinate-resonant. This is the
finite algebraic shadow of the draft's warning that joint diagonal resonances and
per-coordinate resonances are different columns. -/
theorem pairCancel_not_coordinateResonant :
    ¬ coordinateResonant pairCancelFrequencies pairCancelRelation := by
  intro h
  have h0 := h (0 : Fin 2)
  unfold coordinateResonant pairCancelRelation pairCancelFrequencies at h0
  norm_num at h0

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- The finite-support diagonal relation lattice attached to a frequency family. -/
def diagonalRelationLattice {ι A : Type*} [AddCommGroup A] (ω : ι → A) : Set (ι →₀ ℤ) :=
  {m | diagonalResonant ω m}

/-- The arithmetic prime-log diagonal relation lattice is trivial. This is the
finite-character `Λ = 0` vertex of the prime torus: no nonzero algebraic
character annihilates the arithmetic diagonal frequencies. -/
theorem primeLog_diagonalRelationLattice_eq_singleton :
    diagonalRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)) = {0} := by
  ext m
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (logPrime_diagonalResonant_eq_zero h)
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst m
    unfold diagonalRelationLattice diagonalResonant
    simp

/-- Every finite slice of the arithmetic prime-log annihilator is also trivial.
The finite support hypothesis is included to match the finite-torus truncations
used in the inverse-Galois queue item; the actual triviality comes from unique
factorization/log-prime independence. -/
def finitePrimeLogAnnihilator (S : Finset Nat.Primes) : Set (Nat.Primes →₀ ℤ) :=
  {m | m.support ⊆ S ∧ diagonalResonant (fun p : Nat.Primes => Real.log (p : ℕ)) m}

theorem finitePrimeLogAnnihilator_eq_singleton (S : Finset Nat.Primes) :
    finitePrimeLogAnnihilator S = {0} := by
  ext m
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (logPrime_diagonalResonant_eq_zero h.2)
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst m
    unfold finitePrimeLogAnnihilator diagonalResonant
    simp

end

end GaloisForLFunctions
