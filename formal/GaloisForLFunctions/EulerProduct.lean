import GaloisForLFunctions.Core

/-!
# The field's First Theorem: Euler product ⟺ Bohr-lift factorization (Tier A)

`hypertranscendental_galois_field_foundations.md` §9 ("the field's FIRST THEOREM"):
a Dirichlet series `D(s) = Σ aₙ n^{-s}` has an **Euler product** iff its **Bohr lift
factors over the prime coordinates** iff it is a single irreducible tensor difference
module. The pre-spectral firewall: a series with no Euler product (a non-multiplicative
`aₙ`) does not factor, and this is detectable at a finite `n` — *before any zero is
examined*. The known fakes (Davenport–Heilbronn, Epstein) are non-multiplicative and so
fall on the wrong side of this dichotomy.

Here the Dirichlet coefficients are modelled by `ArithmeticFunction ℂ` (`ℕ → ℂ` with
`a 0 = 0`, `a 1 = 1` the normalization), and "Bohr lift factors over primes" is exactly
the multiplicative factorization `aₙ = ∏_{p ∣ n} a(p^{vₚ(n)})`.

* `isMultiplicative_iff_bohr_factorization` — the First Theorem (both directions).
  The forward direction is mathlib's `IsMultiplicative.multiplicative_factorization`; the
  converse (factorization ⟹ multiplicative) is the new content, via disjointness of the
  prime supports for coprime arguments (`Finsupp.prod_add_index_of_disjoint`).
* `fake_fails_factorization` — the firewall: a normalized non-multiplicative series fails
  the prime factorization at some finite `n` (no Euler product, witnessed pre-spectrally).

This is rigorous and pre-spectral. It encodes no zero, no positivity, no RH. The
representation-theoretic spine ("irreducible ⟺ Euler product ⟺ maximal `G_L`-orbit") and
its conjectural consequence (DSS/RH) are NOT formalized and remain frontier statements.
-/

open scoped BigOperators

open ArithmeticFunction

namespace GaloisForLFunctions

noncomputable section

/-- **The field's First Theorem (Euler product ⟺ Bohr-lift factorization).**
A Dirichlet coefficient function `f` is multiplicative (has an Euler product) iff it is
normalized `f 1 = 1` and its Bohr lift factors over the prime coordinates, i.e.
`f n = ∏_{p ∣ n} f (p ^ vₚ(n))` for every `n ≠ 0`. -/
theorem isMultiplicative_iff_bohr_factorization (f : ArithmeticFunction ℂ) :
    f.IsMultiplicative ↔
      (f 1 = 1 ∧ ∀ n : ℕ, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k)) := by
  constructor
  · intro hf
    exact ⟨hf.map_one, fun n hn =>
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hf hn⟩
  · rintro ⟨h1, hfact⟩
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨h1, ?_⟩
    intro m n hm hn hcop
    have hdisj : Disjoint m.factorization.support n.factorization.support := by
      rw [Nat.support_factorization, Nat.support_factorization]
      exact hcop.disjoint_primeFactors
    rw [hfact (m * n) (Nat.mul_ne_zero hm hn), hfact m hm, hfact n hn,
        Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint hdisj]

/-- **The pre-spectral firewall.** A normalized (`f 1 = 1`) Dirichlet series with **no
Euler product** (non-multiplicative `f`) fails the prime factorization at some finite `n`:
there is `n ≠ 0` with `f n ≠ ∏_{p ∣ n} f (p ^ vₚ(n))`. The failure of the Euler product is
witnessed at a finite `n`, before any zero is examined — the fake-family obstruction made
intrinsic and pre-spectral. -/
theorem fake_fails_factorization (f : ArithmeticFunction ℂ)
    (h1 : f 1 = 1) (hnm : ¬ f.IsMultiplicative) :
    ∃ n : ℕ, n ≠ 0 ∧ f n ≠ n.factorization.prod fun p k => f (p ^ k) := by
  by_contra h
  push Not at h
  exact hnm ((isMultiplicative_iff_bohr_factorization f).mpr ⟨h1, h⟩)

/-- The real part of the primitive order-4 Dirichlet character modulo `5`, as used
in the Davenport-Heilbronn-style fake-family witness: residues `1,4` have real
parts `1,-1`, and residues `0,2,3` have real part `0`. -/
def davenportHeilbronnFakeCoeffInt (n : ℕ) : ℤ :=
  match n % 5 with
  | 1 => 1
  | 4 => -1
  | _ => 0

/-- The corresponding normalized arithmetic-function coefficient model over `ℂ`.
This is only the finite coefficient firewall witness, not a formalization of the
Davenport-Heilbronn function, its functional equation, or its zeros. -/
def davenportHeilbronnFakeCoeff : ArithmeticFunction ℂ :=
  ZeroHom.mk (fun n => (davenportHeilbronnFakeCoeffInt n : ℂ)) (by
    norm_num [davenportHeilbronnFakeCoeffInt])

/-- **Concrete fake-family firewall witness.** The mod-5 Davenport-Heilbronn-style
coefficient model is not multiplicative: `a_6 = 1` but `a_2 a_3 = 0`. This is the
finite, pre-spectral obstruction behind the chat computation; it examines no zeros
and proves no RH/GRH localization statement. -/
theorem davenportHeilbronnFakeCoeff_not_isMultiplicative :
    ¬ davenportHeilbronnFakeCoeff.IsMultiplicative := by
  intro hmul
  have h23 : davenportHeilbronnFakeCoeff (2 * 3)
      = davenportHeilbronnFakeCoeff 2 * davenportHeilbronnFakeCoeff 3 :=
    hmul.2 (by norm_num : Nat.Coprime 2 3)
  norm_num [davenportHeilbronnFakeCoeff, davenportHeilbronnFakeCoeffInt] at h23

end

end GaloisForLFunctions
