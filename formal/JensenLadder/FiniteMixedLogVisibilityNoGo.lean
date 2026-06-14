import JensenLadder.FiniteEulerProductMixedLogGate
import JensenLadder.FiniteMultiplicityVisibilityNoGo

/-!
# Finite mixed-log visibility no-go

This file formalizes a finite obstruction for mixed-log carrier packets.

A finite packet of mixed-log cancellations only enforces the rows it sees.  If
the packet cleanly misses a coprime product `m*n`, a product-spike fake can
satisfy every visible mixed-log row while failing the global coprime mixed-log
row at `(m,n)`.

This is not an RH proof and not a global domination theorem.  It is a finite
fake-gate no-go for packet designs that are prime-flavored but do not visibly
carry the needed mixed convolution row.

Evidence class: proved finite algebra lemma.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace FiniteMixedLogVisibilityNoGo

open FiniteEulerProductMixedLogGate
open FiniteMultiplicityVisibilityNoGo

/-- A finite mixed-log packet is cleanly missing the product index `m*n` if no
visible pair uses `m*n` as a coordinate or as its product. -/
def CleanlyMissesProduct (R : Finset (ℕ × ℕ)) (m n : ℕ) : Prop :=
  ∀ uv : ℕ × ℕ, uv ∈ R ->
    uv.1 * uv.2 ≠ m * n ∧ uv.1 ≠ m * n ∧ uv.2 ≠ m * n

/-- If a mixed-log row cleanly misses the spiked product, the product-spike fake
has zero mixed log coefficient on that row. -/
theorem productSpike_mixedLogCoeffOf_eq_zero_of_cleanly_misses
    {m n : ℕ} {uv : ℕ × ℕ}
    (hprod : uv.1 * uv.2 ≠ m * n)
    (hleft : uv.1 ≠ m * n)
    (hright : uv.2 ≠ m * n) :
    mixedLogCoeffOf (productSpike m n) uv.1 uv.2 = 0 := by
  unfold mixedLogCoeffOf mixedLogCoeff productSpike
  simp [hprod, hleft, hright]

/-- A product-spike fake satisfies every visible mixed-log row in a packet that
cleanly misses its spiked product. -/
theorem productSpike_mixedLogCancellationOn_of_cleanly_misses
    {R : Finset (ℕ × ℕ)} {m n : ℕ}
    (hclean : CleanlyMissesProduct R m n) :
    MixedLogCancellationOn R (productSpike m n) := by
  intro uv huv
  rcases hclean uv huv with ⟨hprod, hleft, hright⟩
  exact productSpike_mixedLogCoeffOf_eq_zero_of_cleanly_misses
    (m := m) (n := n) (uv := uv) hprod hleft hright

/-- The product-spike fake is not coprime mixed-log free at its own coprime pair. -/
theorem productSpike_not_coprimeMixedLogFree
    {m n : ℕ}
    (hcop : Nat.Coprime m n)
    (hm_ne : m ≠ m * n)
    (hn_ne : n ≠ m * n) :
    ¬ CoprimeMixedLogFree (productSpike m n) := by
  intro hfree
  have hzero : mixedLogCoeffOf (productSpike m n) m n = 0 := hfree m n hcop
  have hcoeff : mixedLogCoeffOf (productSpike m n) m n = -1 := by
    unfold mixedLogCoeffOf mixedLogCoeff productSpike
    simp [hm_ne, hn_ne]
  rw [hcoeff] at hzero
  norm_num at hzero

/-- A finite mixed-log packet that cleanly misses a coprime product cannot force
the global coprime mixed-log row. -/
theorem finiteMixedLogPacket_cannot_force_coprimeMixedLogFree_cleanly_missing
    {R : Finset (ℕ × ℕ)} {m n : ℕ}
    (hclean : CleanlyMissesProduct R m n)
    (hcop : Nat.Coprime m n)
    (hm_ne : m ≠ m * n)
    (hn_ne : n ≠ m * n) :
    ∃ a : ℕ -> ℝ,
      MixedLogCancellationOn R a ∧ ¬ CoprimeMixedLogFree a := by
  exact ⟨productSpike m n,
    productSpike_mixedLogCancellationOn_of_cleanly_misses hclean,
    productSpike_not_coprimeMixedLogFree hcop hm_ne hn_ne⟩

/-- Concrete `(2,3,6)` corollary: a packet that cleanly misses the index `6`
cannot force the global coprime mixed-log row. -/
theorem finiteMixedLogPacket_missing_clean_six_cannot_force_coprimeMixedLogFree
    {R : Finset (ℕ × ℕ)}
    (hclean6 : ∀ uv : ℕ × ℕ, uv ∈ R ->
      uv.1 * uv.2 ≠ 6 ∧ uv.1 ≠ 6 ∧ uv.2 ≠ 6) :
    ∃ a : ℕ -> ℝ,
      MixedLogCancellationOn R a ∧ ¬ CoprimeMixedLogFree a := by
  have hclean : CleanlyMissesProduct R 2 3 := by
    intro uv huv
    have h := hclean6 uv huv
    norm_num
    exact h
  exact finiteMixedLogPacket_cannot_force_coprimeMixedLogFree_cleanly_missing
    (R := R) (m := 2) (n := 3) hclean (by decide) (by norm_num) (by norm_num)

end FiniteMixedLogVisibilityNoGo
end JensenLadder

