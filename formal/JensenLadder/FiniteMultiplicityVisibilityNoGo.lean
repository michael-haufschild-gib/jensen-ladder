import JensenLadder.DHMultiplicityFakeGate

/-!
# Finite multiplicativity visibility no-go

This file formalizes a small design obstruction for finite carrier packets.

If a finite coefficient predicate only sees a set `S` of indices and `S` does
not contain a product `m*n`, then the predicate cannot force the coprime
multiplicativity relation at `(m,n)`.  A fake stream can agree with the zeta
unit stream on every visible index, pass the same visible predicate, and still
break multiplicativity at the hidden product.

This is not a proof of RH or of the carrier domination theorem.  It is a finite
fake-gate no-go: a packet that claims to use Euler-product multiplicativity must
visibly include product relations, or the claim replays on a nonmultiplicative
fake.

Evidence class: proved finite arithmetic lemma.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace FiniteMultiplicityVisibilityNoGo

open DHMultiplicityFakeGate

/-- Two coefficient streams agree on a finite visible set. -/
def AgreementOn (S : Finset ℕ) (a b : ℕ -> ℝ) : Prop :=
  ∀ k : ℕ, k ∈ S -> a k = b k

/-- A predicate on coefficient streams only sees the coefficients indexed by `S`. -/
def VisiblePredicate (S : Finset ℕ) (P : (ℕ -> ℝ) -> Prop) : Prop :=
  ∀ a b : ℕ -> ℝ, AgreementOn S a b -> (P a ↔ P b)

/-- The zeta unit coefficient stream. -/
def zetaUnit : ℕ -> ℝ := fun _ => 1

/-- A fake stream which agrees with zeta except at the product `m*n`. -/
def productSpike (m n : ℕ) : ℕ -> ℝ :=
  fun k => if k = m * n then 0 else 1

/-- If the product index is not visible, the product-spike stream agrees with
the zeta unit stream on the visible set. -/
theorem productSpike_agrees_zetaUnit_on_of_product_not_mem
    {S : Finset ℕ} {m n : ℕ}
    (hmn : m * n ∉ S) :
    AgreementOn S (productSpike m n) zetaUnit := by
  intro k hk
  unfold productSpike zetaUnit
  by_cases h : k = m * n
  · subst k
    exact False.elim (hmn hk)
  · simp [h]

/-- The product-spike stream breaks coprime multiplicativity at `(m,n)`. -/
theorem productSpike_not_coprimeMultiplicative
    {m n : ℕ}
    (hcop : Nat.Coprime m n)
    (hm_ne : m ≠ m * n)
    (hn_ne : n ≠ m * n) :
    ¬ CoprimeMultiplicative (productSpike m n) := by
  intro hmul
  have hbad := hmul m n hcop
  have hprod : productSpike m n (m * n) = 0 := by
    simp [productSpike]
  have hmval : productSpike m n m = 1 := by
    simp [productSpike, hm_ne]
  have hnval : productSpike m n n = 1 := by
    simp [productSpike, hn_ne]
  rw [hprod, hmval, hnval] at hbad
  norm_num at hbad

/--
If a finite visible predicate certifies the zeta unit stream while missing a
product index, then it also certifies a nonmultiplicative fake stream.
-/
theorem visiblePredicate_cannot_force_coprimeMultiplicative_missingProduct
    {S : Finset ℕ} {P : (ℕ -> ℝ) -> Prop} {m n : ℕ}
    (hvisible : VisiblePredicate S P)
    (hzeta : P zetaUnit)
    (hmn_not_mem : m * n ∉ S)
    (hcop : Nat.Coprime m n)
    (hm_ne : m ≠ m * n)
    (hn_ne : n ≠ m * n) :
    ∃ a : ℕ -> ℝ,
      AgreementOn S a zetaUnit ∧ P a ∧ ¬ CoprimeMultiplicative a := by
  let a := productSpike m n
  have hagree : AgreementOn S a zetaUnit :=
    productSpike_agrees_zetaUnit_on_of_product_not_mem hmn_not_mem
  have hPa : P a := (hvisible a zetaUnit hagree).2 hzeta
  have hnot : ¬ CoprimeMultiplicative a :=
    productSpike_not_coprimeMultiplicative hcop hm_ne hn_ne
  exact ⟨a, hagree, hPa, hnot⟩

/--
Concrete `(2,3,6)` corollary: a finite visible predicate that does not see
`a_6` cannot force the first zeta/DH multiplicativity separator.
-/
theorem visiblePredicate_missing_six_cannot_force_coprimeMultiplicative
    {S : Finset ℕ} {P : (ℕ -> ℝ) -> Prop}
    (hvisible : VisiblePredicate S P)
    (hzeta : P zetaUnit)
    (h6 : 6 ∉ S) :
    ∃ a : ℕ -> ℝ,
      AgreementOn S a zetaUnit ∧ P a ∧ ¬ CoprimeMultiplicative a := by
  have hmn_not_mem : 2 * 3 ∉ S := by
    norm_num
    exact h6
  exact visiblePredicate_cannot_force_coprimeMultiplicative_missingProduct
    (S := S) (P := P) (m := 2) (n := 3)
    hvisible hzeta hmn_not_mem (by decide) (by norm_num) (by norm_num)

end FiniteMultiplicityVisibilityNoGo
end JensenLadder

namespace JensenLadder
namespace FiniteMultiplicityVisibilityNoGo

/-- A finite visible set that contains only prime indices cannot force the first
`(2,3,6)` multiplicativity relation. -/
theorem visiblePredicate_primeOnly_cannot_force_coprimeMultiplicative
    {S : Finset ℕ} {P : (ℕ -> ℝ) -> Prop}
    (hprimeOnly : ∀ k : ℕ, k ∈ S -> Nat.Prime k)
    (hvisible : VisiblePredicate S P)
    (hzeta : P zetaUnit) :
    ∃ a : ℕ -> ℝ,
      AgreementOn S a zetaUnit ∧ P a ∧
        ¬ DHMultiplicityFakeGate.CoprimeMultiplicative a := by
  have h6 : 6 ∉ S := by
    intro hmem
    have hp6 : Nat.Prime 6 := hprimeOnly 6 hmem
    norm_num at hp6
  exact visiblePredicate_missing_six_cannot_force_coprimeMultiplicative
    hvisible hzeta h6

end FiniteMultiplicityVisibilityNoGo
end JensenLadder

namespace JensenLadder
namespace FiniteMultiplicityVisibilityNoGo

/-- If a visible set excludes products of distinct primes, then it cannot force
multiplicativity at any such excluded product. -/
theorem visiblePredicate_noDistinctPrimeProducts_cannot_force_coprimeMultiplicative
    {S : Finset ℕ} {P : (ℕ -> ℝ) -> Prop}
    (hnoProducts :
      ∀ p q : ℕ, Nat.Prime p -> Nat.Prime q -> p ≠ q -> p * q ∉ S)
    (hvisible : VisiblePredicate S P)
    (hzeta : P zetaUnit) :
    ∃ a : ℕ -> ℝ,
      AgreementOn S a zetaUnit ∧ P a ∧
        ¬ DHMultiplicityFakeGate.CoprimeMultiplicative a := by
  have h6 : 6 ∉ S := by
    have h23 : 2 * 3 ∉ S :=
      hnoProducts 2 3 (by decide) (by decide) (by norm_num)
    norm_num at h23
    exact h23
  exact visiblePredicate_missing_six_cannot_force_coprimeMultiplicative
    hvisible hzeta h6

end FiniteMultiplicityVisibilityNoGo
end JensenLadder
