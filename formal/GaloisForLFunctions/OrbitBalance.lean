import GaloisForLFunctions.Core

/-!
# Orbit-balance: finite augmentation-kernel algebra

This file formalizes the elementary finite-support algebra behind the
`σ`-orbit-balance criterion in
`docs/drafts/pipeline/2-fully-proven/two-sources-of-hypertranscendence.md`.

On a single orbit, a rational divisor is modeled by a finitely supported
integer-valued function. The orbit degree is the augmentation map, and a
degree-zero finite divisor decomposes as a finite sum of balanced point-masses
against any chosen base point.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- The finite orbit-degree/augmentation of an integer-valued finitely
supported divisor on an orbit. -/
def orbitDegree {α : Type*} (D : α →₀ ℤ) : ℤ :=
  D.sum (fun _ n => n)

/-- The zero finite divisor has orbit degree zero. -/
theorem orbitDegree_zero {α : Type*} : orbitDegree (0 : α →₀ ℤ) = 0 := by
  simp [orbitDegree]

/-- The orbit degree of a single point-mass is its coefficient. -/
theorem orbitDegree_single {α : Type*} (a : α) (n : ℤ) :
    orbitDegree (Finsupp.single a n) = n := by
  simp [orbitDegree]

/-- Orbit degree is additive on finite divisors. -/
theorem orbitDegree_add {α : Type*} (D E : α →₀ ℤ) :
    orbitDegree (D + E) = orbitDegree D + orbitDegree E := by
  rw [orbitDegree, Finsupp.sum_add_index']
  · rfl
  · intro a
    rfl
  · intro a b c
    rfl

/-- Orbit degree is compatible with subtraction. -/
theorem orbitDegree_sub {α : Type*} (D E : α →₀ ℤ) :
    orbitDegree (D - E) = orbitDegree D - orbitDegree E := by
  rw [orbitDegree]
  exact Finsupp.sum_sub_index (h := fun _ n => n) (by intro a b c; rfl)

/-- A finite divisor with nonzero orbit degree cannot equal a degree-zero
divisor. This is the algebraic core of the "non-CC is not in the CC subgroup"
separation after passing to the orbit-degree classifier. -/
theorem orbitDegree_ne_zero_ne_of_orbitDegree_zero {α : Type*} {D E : α →₀ ℤ}
    (hD : orbitDegree D ≠ 0) (hE : orbitDegree E = 0) : D ≠ E := by
  intro h
  exact hD (by rw [h, hE])

/-- A nonzero point-mass on one orbit cannot equal any degree-zero finite
divisor. The degree-one case models the archimedean `Γ` orbit imbalance against
zero-degree prime/CC classes. -/
theorem orbitDegree_single_ne_zero_ne_of_orbitDegree_zero {α : Type*}
    (a : α) {n : ℤ} (hn : n ≠ 0) {E : α →₀ ℤ} (hE : orbitDegree E = 0) :
    Finsupp.single a n ≠ E := by
  have hdeg : orbitDegree (Finsupp.single a n) ≠ 0 := by
    simpa [orbitDegree_single] using hn
  exact orbitDegree_ne_zero_ne_of_orbitDegree_zero hdeg hE

/-- A balanced point-mass `n[a]-n[b]` has orbit degree zero. -/
theorem orbitDegree_single_sub_single {α : Type*} [DecidableEq α] (a b : α) (n : ℤ) :
    orbitDegree (Finsupp.single a n - Finsupp.single b n) = 0 := by
  by_cases hab : a = b
  · subst hab
    simp [orbitDegree]
  · rw [orbitDegree, Finsupp.sum_sub_index]
    · simp
    · intro x y z
      rfl

/-- **Finite orbit-balance decomposition.** If an integer-valued finite divisor
has orbit degree zero, then it is a finite sum of balanced point-masses against
any chosen base point. This is the augmentation-kernel core of the paper
statement that degree-zero finite orbit divisors telescope. -/
theorem eq_sum_single_sub_base_of_orbitDegree_zero {α : Type*} [DecidableEq α]
    (base : α) (D : α →₀ ℤ) (hD : orbitDegree D = 0) :
    D = D.support.sum (fun a => Finsupp.single a (D a) - Finsupp.single base (D a)) := by
  have hbase : D.support.sum (fun a => Finsupp.single base (D a)) = (0 : α →₀ ℤ) := by
    ext x
    by_cases hx : x = base
    · subst hx
      simpa [orbitDegree] using hD
    · simp [hx]
  calc
    D = D.support.sum (fun a => Finsupp.single a (D a)) := by
      simpa [Finsupp.sum] using (Finsupp.sum_single D).symm
    _ = D.support.sum (fun a => Finsupp.single a (D a) - Finsupp.single base (D a)) := by
      rw [Finset.sum_sub_distrib, hbase, sub_zero]

/-- The finite shift-coboundary on the integer orbit, written as a sum of
consecutive differences `[z-1]-[z]`. This is the model for
`div(g(z+1)/g(z))` on one shift orbit. -/
def intShiftCoboundary (E : ℤ →₀ ℤ) : ℤ →₀ ℤ :=
  E.support.sum (fun z => Finsupp.single (z - 1) (E z) - Finsupp.single z (E z))

/-- A single consecutive shift-difference term `[z-1]-[z]` with coefficient
`n`. -/
def intShiftTerm (z n : ℤ) : ℤ →₀ ℤ :=
  Finsupp.single (z - 1) n - Finsupp.single z n

/-- Every finite integer-orbit shift-coboundary has orbit degree zero. This is
the `im(Δ) ⊆ ker(deg)` half of the divisor telescoping criterion. -/
theorem orbitDegree_intShiftCoboundary (E : ℤ →₀ ℤ) :
    orbitDegree (intShiftCoboundary E) = 0 := by
  unfold intShiftCoboundary
  induction E.support using Finset.induction_on with
  | empty => simp [orbitDegree_zero]
  | insert z s hzs ih =>
      rw [Finset.sum_insert hzs]
      rw [orbitDegree_add]
      rw [orbitDegree_sub]
      rw [orbitDegree_single, orbitDegree_single, ih]
      ring

/-- Telescoping along a rightward finite path on the integer orbit. The
balanced divisor `n[base+k]-n[base]` is a finite sum of consecutive
shift-differences. This is a concrete `ker(deg) ⊆ im(Δ)` fragment. -/
theorem sum_intShiftTerm_right (base : ℤ) (k : ℕ) (n : ℤ) :
    (Finset.range k).sum (fun j => intShiftTerm (base + (j.succ : ℤ)) (-n)) =
      Finsupp.single (base + (k : ℤ)) n - Finsupp.single base n := by
  induction k with
  | zero =>
      simp [intShiftTerm]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : base + ((k : ℤ) + 1) - 1 = base + (k : ℤ) := by
        ring
      ext x
      simp [intShiftTerm, hstep]
      abel

end

end GaloisForLFunctions
