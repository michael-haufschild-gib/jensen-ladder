import GaloisForLFunctions.Core

/-!
# Archimedean corank no-collapse

This file formalizes the finite-slice linear algebra behind
`archimedean-corank-no-collapse.md`.

The prime-log family is already `ℚ`-linearly independent in `Core`.  A finite
archimedean/product-formula generator supported on a finite prime slice is a
`ℚ`-linear combination of those prime logarithms, so adjoining it does not change
the slice span or reduce the slice rank.  Since finite prime slices exist with
arbitrarily large cardinality, no finite dependent archimedean enrichment can
collapse the prime-log corank to a finite rank.

This is the exact algebraic no-collapse layer.  It does not construct an
infinite-dimensional torus, a completed product-formula operator, or an `F₁`
realization object.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The `ℚ`-span of the prime logarithms in a finite prime slice. -/
def primeLogSpan (S : Finset Nat.Primes) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range fun p : S => Real.log ((p : Nat.Primes) : ℕ))

/-- Finite slices of the prime-log family remain linearly independent. -/
theorem primeLogFiniteSlice_linearIndependent (S : Finset Nat.Primes) :
    LinearIndependent ℚ (fun p : S => Real.log ((p : Nat.Primes) : ℕ)) := by
  exact linearIndependent_log_primes.comp (fun p : S => (p : Nat.Primes)) Subtype.coe_injective

/-- Every finite prime slice has full rational rank. -/
theorem primeLogFiniteSlice_finrank (S : Finset Nat.Primes) :
    Module.finrank ℚ (primeLogSpan S) = S.card := by
  unfold primeLogSpan
  rw [finrank_span_eq_card (primeLogFiniteSlice_linearIndependent S)]
  exact Fintype.card_coe S

/-- A finite archimedean/product-formula generator supported on `S`: a rational
linear combination of the prime logarithms in that slice. -/
def archimedeanFiniteGenerator (S : Finset Nat.Primes) (a : S → ℚ) : ℝ :=
  ∑ p : S, a p • Real.log ((p : Nat.Primes) : ℕ)

/-- The finite archimedean generator is already in the prime-log span. -/
theorem archimedeanFiniteGenerator_mem_primeLogSpan
    (S : Finset Nat.Primes) (a : S → ℚ) :
    archimedeanFiniteGenerator S a ∈ primeLogSpan S := by
  classical
  unfold archimedeanFiniteGenerator primeLogSpan
  refine Submodule.sum_mem _ ?_
  intro p _hp
  exact Submodule.smul_mem _ (a p) (Submodule.subset_span ⟨p, rfl⟩)

/-- Adjoining a finite archimedean generator does not change the finite
prime-log span. -/
theorem primeLogSpan_insert_archimedean_eq
    (S : Finset Nat.Primes) (a : S → ℚ) :
    Submodule.span ℚ
      (Set.insert (archimedeanFiniteGenerator S a)
        (Set.range fun p : S => Real.log ((p : Nat.Primes) : ℕ))) = primeLogSpan S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact archimedeanFiniteGenerator_mem_primeLogSpan S a
    · unfold primeLogSpan
      exact Submodule.subset_span hx
  · unfold primeLogSpan
    exact Submodule.span_mono (Set.subset_insert _ _)

/-- Consequently, the same finite slice keeps full rank after adjoining that
finite dependent archimedean generator. -/
theorem primeLogFiniteSlice_finrank_with_archimedean
    (S : Finset Nat.Primes) (a : S → ℚ) :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.insert (archimedeanFiniteGenerator S a)
          (Set.range fun p : S => Real.log ((p : Nat.Primes) : ℕ)))) = S.card := by
  rw [primeLogSpan_insert_archimedean_eq, primeLogFiniteSlice_finrank]

/-- Prime-log finite-slice ranks are unbounded. This is the finite-slice form of
`corank = ∞`. -/
theorem primeLogFiniteSlice_finrank_unbounded (N : ℕ) :
    ∃ S : Finset Nat.Primes, N ≤ Module.finrank ℚ (primeLogSpan S) := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq Nat.Primes N
  refine ⟨S, ?_⟩
  rw [primeLogFiniteSlice_finrank, hS]

/-- Even after adjoining a dependent finite archimedean generator, the
finite-slice ranks remain unbounded. This is the formal no-collapse statement:
finite dependent archimedean enrichment cannot collapse the infinite prime
corank to finite rank. -/
theorem primeLogFiniteSlice_finrank_with_archimedean_unbounded (N : ℕ) :
    ∃ (S : Finset Nat.Primes) (a : S → ℚ),
      N ≤ Module.finrank ℚ
        (Submodule.span ℚ
          (Set.insert (archimedeanFiniteGenerator S a)
            (Set.range fun p : S => Real.log ((p : Nat.Primes) : ℕ)))) := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq Nat.Primes N
  refine ⟨S, fun _ => 0, ?_⟩
  rw [primeLogFiniteSlice_finrank_with_archimedean, hS]

/-- The full `ℚ`-span of all prime logarithms. -/
def primeLogFullSpan : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range fun p : Nat.Primes => Real.log (p : ℕ))

/-- The full prime-log span has rank equal to the cardinality of the prime set. -/
theorem primeLogFullSpan_rank :
    Module.rank ℚ primeLogFullSpan = Cardinal.mk Nat.Primes := by
  unfold primeLogFullSpan
  rw [rank_span linearIndependent_log_primes]
  exact Cardinal.mk_range_eq _ linearIndependent_log_primes.injective

/-- A finite archimedean generator is also in the full prime-log span. -/
theorem archimedeanFiniteGenerator_mem_primeLogFullSpan
    (S : Finset Nat.Primes) (a : S → ℚ) :
    archimedeanFiniteGenerator S a ∈ primeLogFullSpan := by
  exact (Submodule.span_mono (by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    exact ⟨(p : Nat.Primes), rfl⟩)) (archimedeanFiniteGenerator_mem_primeLogSpan S a)

/-- Adjoining a finite dependent archimedean generator does not change the full
prime-log span. -/
theorem primeLogFullSpan_insert_archimedean_eq
    (S : Finset Nat.Primes) (a : S → ℚ) :
    Submodule.span ℚ
      (Set.insert (archimedeanFiniteGenerator S a)
        (Set.range fun p : Nat.Primes => Real.log (p : ℕ))) = primeLogFullSpan := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact archimedeanFiniteGenerator_mem_primeLogFullSpan S a
    · unfold primeLogFullSpan
      exact Submodule.subset_span hx
  · unfold primeLogFullSpan
    exact Submodule.span_mono (Set.subset_insert _ _)

/-- The full rank remains the prime-set rank after adjoining a finite dependent
archimedean generator: the formal `corank = ∞` no-collapse statement. -/
theorem primeLogFullSpan_rank_with_archimedean
    (S : Finset Nat.Primes) (a : S → ℚ) :
    Module.rank ℚ
      (Submodule.span ℚ
        (Set.insert (archimedeanFiniteGenerator S a)
          (Set.range fun p : Nat.Primes => Real.log (p : ℕ)))) = Cardinal.mk Nat.Primes := by
  rw [primeLogFullSpan_insert_archimedean_eq, primeLogFullSpan_rank]

end

end GaloisForLFunctions
