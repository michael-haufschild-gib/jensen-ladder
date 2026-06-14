import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits

/-!
# Sturm certificate core

This file starts the GPT-owned Sturm layer for finite Jensen certificates.
It formalizes the first reusable endpoint: a continuous real function with a
certified sign change on a bracket interval has a real zero in that interval.

Later certificate files can specialize `f` to a real polynomial and pair these
brackets with a degree/root-count argument to prove finite-section
hyperbolicity.
-/

namespace JensenLadder
namespace Sturm

open Set Polynomial

/--
A closed bracket whose endpoint values straddle zero, allowing either endpoint
orientation. This matches certificate rows where the sign orientation is stored
per bracket.
-/
def HasSignChangeOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (f a ≤ 0 ∧ 0 ≤ f b) ∨ (0 ≤ f a ∧ f b ≤ 0)

/--
Closed-interval sign-change certificate, increasing orientation.

If `f a <= 0 <= f b` and `f` is continuous on `[a,b]`, then `f` has a zero in
that certified bracket.
-/
theorem exists_zero_of_nonpos_nonneg
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ 0)
    (hb : 0 ≤ f b) :
    ∃ x ∈ Icc a b, f x = 0 := by
  have h0 : 0 ∈ Icc (f a) (f b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hf h0 with ⟨x, hxmem, hx⟩
  exact ⟨x, hxmem, hx⟩

/--
Closed-interval sign-change certificate, decreasing orientation.

This is the same IVT endpoint with endpoint signs reversed.
-/
theorem exists_zero_of_nonneg_nonpos
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : 0 ≤ f a)
    (hb : f b ≤ 0) :
    ∃ x ∈ Icc a b, f x = 0 := by
  have h0 : 0 ∈ Icc (f b) (f a) := ⟨hb, ha⟩
  rcases intermediate_value_Icc' hab hf h0 with ⟨x, hxmem, hx⟩
  exact ⟨x, hxmem, hx⟩

/--
Strict increasing-orientation variant used by rational interval certificates.
-/
theorem exists_zero_of_neg_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : f a < 0)
    (hb : 0 < f b) :
    ∃ x ∈ Icc a b, f x = 0 :=
  exists_zero_of_nonpos_nonneg hab hf ha.le hb.le

/--
Strict decreasing-orientation variant used by rational interval certificates.
-/
theorem exists_zero_of_pos_neg
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : 0 < f a)
    (hb : f b < 0) :
    ∃ x ∈ Icc a b, f x = 0 :=
  exists_zero_of_nonneg_nonpos hab hf ha.le hb.le

/--
Closed-interval sign-change certificate with endpoint orientation supplied as
data.
-/
theorem exists_zero_of_hasSignChangeOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hsign : HasSignChangeOn f a b) :
    ∃ x ∈ Icc a b, f x = 0 := by
  rcases hsign with h | h
  · exact exists_zero_of_nonpos_nonneg hab hf h.1 h.2
  · exact exists_zero_of_nonneg_nonpos hab hf h.1 h.2

/--
Multiple disjoint sign brackets give pairwise distinct certified roots.

This is the first certificate-level Sturm endpoint: after the numeric side
supplies disjoint rational brackets, endpoint sign checks, and continuity for a
real function `f`, Lean packages one root in every bracket and proves those
roots are pairwise distinct.
-/
theorem exists_pairwise_distinct_roots_of_sign_changes
    {ι : Type*} {f : ℝ → ℝ} {L R : ι → ℝ}
    (hdisj : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j)))
    (hbracket : ∀ i, L i ≤ R i)
    (hcont : ∀ i, ContinuousOn f (Icc (L i) (R i)))
    (hsign : ∀ i, HasSignChangeOn f (L i) (R i)) :
    ∃ x : ι → ℝ,
      (∀ i, x i ∈ Icc (L i) (R i) ∧ f (x i) = 0) ∧
      Pairwise (fun i j => x i ≠ x j) := by
  classical
  have hroot : ∀ i, ∃ x ∈ Icc (L i) (R i), f x = 0 := by
    intro i
    exact exists_zero_of_hasSignChangeOn (hbracket i) (hcont i) (hsign i)
  choose x hxmem hxzero using hroot
  refine ⟨x, ?_, ?_⟩
  · intro i
    exact ⟨hxmem i, hxzero i⟩
  · intro i j hij heq
    have hxi : x i ∈ Icc (L i) (R i) := hxmem i
    have hxj : x i ∈ Icc (L j) (R j) := by
      rw [heq]
      exact hxmem j
    exact (Set.disjoint_left.mp (hdisj hij) hxi hxj)

/--
Degree-filling bracket certificate for real polynomials.

If a nonzero real polynomial of degree at most the number of certified,
pairwise-disjoint sign-change brackets has one bracket root in every bracket,
then those bracket roots account for the entire root multiset of the
polynomial. This is the finite Jensen root-count endpoint: after the numerical
certificate supplies `d` disjoint brackets for a degree-`d` section, no further
real roots or non-real roots can remain.
-/
theorem exists_roots_eq_of_sign_changes
    {ι : Type*} [Fintype ι]
    {p : ℝ[X]} {L R : ι → ℝ}
    (hdisj : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j)))
    (hbracket : ∀ i, L i ≤ R i)
    (hcont : ∀ i, ContinuousOn (fun t : ℝ => p.eval t) (Icc (L i) (R i)))
    (hsign : ∀ i, HasSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i))
    (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ Fintype.card ι) :
    ∃ x : ι → ℝ,
      (∀ i, x i ∈ Icc (L i) (R i) ∧ p.eval (x i) = 0) ∧
      Pairwise (fun i j => x i ≠ x j) ∧
      p.roots = (Finset.univ.image x).val := by
  classical
  rcases exists_pairwise_distinct_roots_of_sign_changes hdisj hbracket hcont hsign with
    ⟨x, hx, hxpair⟩
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact hxpair hne hij
  let S : Finset ℝ := Finset.univ.image x
  have hScard : p.natDegree ≤ S.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ]
    exact hdegree
  have hSroots : ∀ y ∈ S, p.eval y = 0 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
    exact (hx i).2
  have hroots : p.roots = S.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hSroots hScard hp
  exact ⟨x, hx, hxpair, hroots⟩

/--
A full degree-filling sign-bracket certificate makes the real polynomial split
over `ℝ`.

For finite Jensen sections, this is the Lean hyperbolicity endpoint at the
real-polynomial level: if interval arithmetic supplies enough disjoint real
brackets to fill the degree, then `p.Splits`.
-/
theorem splits_of_sign_changes
    {ι : Type*} [Fintype ι]
    {p : ℝ[X]} {L R : ι → ℝ}
    (hdisj : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j)))
    (hbracket : ∀ i, L i ≤ R i)
    (hcont : ∀ i, ContinuousOn (fun t : ℝ => p.eval t) (Icc (L i) (R i)))
    (hsign : ∀ i, HasSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i))
    (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ Fintype.card ι) :
    p.Splits := by
  classical
  rcases exists_roots_eq_of_sign_changes hdisj hbracket hcont hsign hp hdegree with
    ⟨x, _hx, hxpair, hroots⟩
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact hxpair hne hij
  let S : Finset ℝ := Finset.univ.image x
  have hScard : S.card = Fintype.card ι := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ]
  have hrootcard : p.roots.card = S.card := by
    simpa [S] using congrArg Multiset.card hroots
  have hroot_le_nat : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hnat_le_root : p.natDegree ≤ p.roots.card := by
    rw [hrootcard, hScard]
    exact hdegree
  have hcard : p.roots.card = p.natDegree := le_antisymm hroot_le_nat hnat_le_root
  exact (Polynomial.splits_iff_card_roots).2 hcard

/--
`Fin d` specialization of `splits_of_sign_changes`.

This is the intended consumer for generated finite Jensen certificate tables:
row `i : Fin d` supplies one bracket, and the certificate checks
`p.natDegree <= d`.
-/
theorem splits_of_fin_sign_changes
    {d : ℕ} {p : ℝ[X]} {L R : Fin d → ℝ}
    (hdisj : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j)))
    (hbracket : ∀ i, L i ≤ R i)
    (hcont : ∀ i, ContinuousOn (fun t : ℝ => p.eval t) (Icc (L i) (R i)))
    (hsign : ∀ i, HasSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i))
    (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ d) :
    p.Splits := by
  have hdegree' : p.natDegree ≤ Fintype.card (Fin d) := by
    simpa using hdegree
  exact splits_of_sign_changes hdisj hbracket hcont hsign hp hdegree'

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/--
Finite bracket certificate for a real polynomial.

A generated certificate table supplies `d` disjoint brackets, one sign-change
row per `Fin d`, nonzeroness, and a degree bound. Polynomial continuity is
proved internally by the consumer theorem below.
-/
structure FinBracketCertificate (d : ℕ) (p : ℝ[X]) where
  L : Fin d → ℝ
  R : Fin d → ℝ
  disjoint : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j))
  bracket : ∀ i, L i ≤ R i
  sign : ∀ i, HasSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i)
  nonzero : p ≠ 0
  degree_le : p.natDegree ≤ d

/--
A finite bracket certificate proves that the certified polynomial splits over
`ℝ`.

This is the intended proof-level consumer for generated Jensen finite-section
certificate tables: no separate continuity field is required from the table.
-/
theorem FinBracketCertificate.splits {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.Splits := by
  exact splits_of_fin_sign_changes cert.disjoint cert.bracket
    (fun _i => p.continuousOn) cert.sign cert.nonzero cert.degree_le

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/--
Strict endpoint sign-change certificate.

This is the shape most interval-arithmetic sign checks should produce: either
left endpoint negative and right endpoint positive, or the reverse.
-/
def HasStrictSignChangeOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (f a < 0 ∧ 0 < f b) ∨ (0 < f a ∧ f b < 0)

/-- A strict sign-change row is also a weak sign-change row. -/
theorem HasStrictSignChangeOn.hasSignChangeOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hsign : HasStrictSignChangeOn f a b) :
    HasSignChangeOn f a b := by
  rcases hsign with h | h
  · exact Or.inl ⟨h.1.le, h.2.le⟩
  · exact Or.inr ⟨h.1.le, h.2.le⟩

/--
Finite bracket certificate with strict endpoint signs.

This is a convenience wrapper for generated certificates whose sign checks are
strict. It lowers to `FinBracketCertificate` without requiring generated rows
to package non-strict inequalities manually.
-/
structure StrictFinBracketCertificate (d : ℕ) (p : ℝ[X]) where
  L : Fin d → ℝ
  R : Fin d → ℝ
  disjoint : Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j))
  bracket : ∀ i, L i ≤ R i
  strict_sign : ∀ i, HasStrictSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i)
  nonzero : p ≠ 0
  degree_le : p.natDegree ≤ d

/-- Lower a strict-sign certificate to the weak-sign certificate consumer. -/
def StrictFinBracketCertificate.toFinBracketCertificate {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    FinBracketCertificate d p where
  L := cert.L
  R := cert.R
  disjoint := cert.disjoint
  bracket := cert.bracket
  sign := fun i => HasStrictSignChangeOn.hasSignChangeOn (cert.strict_sign i)
  nonzero := cert.nonzero
  degree_le := cert.degree_le

/-- A strict finite bracket certificate proves that the polynomial splits over `ℝ`. -/
theorem StrictFinBracketCertificate.splits {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.Splits := by
  exact cert.toFinBracketCertificate.splits

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Polynomial

/--
If a real polynomial splits over `ℝ`, then complexifying it introduces no new
roots: its complex roots are exactly the image of its real roots.
-/
theorem roots_map_complex_eq_of_splits {p : ℝ[X]}
    (hsplits : p.Splits) :
    p.roots.map (algebraMap ℝ ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
  have hcard : p.roots.card = p.natDegree := by
    exact hsplits.natDegree_eq_card_roots.symm
  exact Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (FaithfulSMul.algebraMap_injective ℝ ℂ) hcard

/-- Every listed complex root of a split real polynomial is the image of a real root. -/
theorem exists_real_of_mem_complex_roots_of_splits {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  have hroots := roots_map_complex_eq_of_splits (p := p) hsplits
  rw [← hroots] at hz
  rcases Multiset.mem_map.mp hz with ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Every complex zero of a nonzero split real polynomial is real. -/
theorem complex_root_is_real_of_splits {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hp
  have hzmem : z ∈ (p.map (algebraMap ℝ ℂ)).roots := by
    exact (Polynomial.mem_roots hpmap).mpr hz
  exact exists_real_of_mem_complex_roots_of_splits hsplits hzmem

/-- Imaginary-part form of `complex_root_is_real_of_splits`. -/
theorem complex_root_im_eq_zero_of_splits {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  rcases complex_root_is_real_of_splits hsplits hp hz with ⟨x, rfl⟩
  simp

/-- Complex-root reality endpoint for weak-sign finite bracket certificates. -/
theorem FinBracketCertificate.complex_root_is_real {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_root_is_real_of_splits cert.splits cert.nonzero hz

/-- Imaginary-part endpoint for weak-sign finite bracket certificates. -/
theorem FinBracketCertificate.complex_root_im_eq_zero {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  exact complex_root_im_eq_zero_of_splits cert.splits cert.nonzero hz

/-- Complex-root reality endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.complex_root_is_real {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_root_is_real_of_splits cert.splits cert.nonzero hz

/-- Imaginary-part endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.complex_root_im_eq_zero {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  exact complex_root_im_eq_zero_of_splits cert.splits cert.nonzero hz

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/--
Root-location endpoint for weak-sign finite bracket certificates.

This exposes the chosen bracket root in every row and the equality between the
polynomial root multiset and the certified row image.
-/
theorem FinBracketCertificate.exists_roots_eq {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∃ x : Fin d → ℝ,
      (∀ i, x i ∈ Icc (cert.L i) (cert.R i) ∧ p.eval (x i) = 0) ∧
      Pairwise (fun i j => x i ≠ x j) ∧
      p.roots = (Finset.univ.image x).val := by
  have hdegree : p.natDegree ≤ Fintype.card (Fin d) := by
    simpa using cert.degree_le
  exact exists_roots_eq_of_sign_changes cert.disjoint cert.bracket
    (fun _i => p.continuousOn) cert.sign cert.nonzero hdegree

/-- Root-location endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.exists_roots_eq {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∃ x : Fin d → ℝ,
      (∀ i, x i ∈ Icc (cert.L i) (cert.R i) ∧ p.eval (x i) = 0) ∧
      Pairwise (fun i j => x i ≠ x j) ∧
      p.roots = (Finset.univ.image x).val := by
  exact cert.toFinBracketCertificate.exists_roots_eq

/--
If every certified bracket starts to the right of zero, then every real root of
the certified polynomial is positive.
-/
theorem FinBracketCertificate.all_roots_positive_of_left_pos {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ p.roots, 0 < y := by
  classical
  rcases cert.exists_roots_eq with ⟨x, hx, _hxpair, hroots⟩
  intro y hy
  rw [hroots] at hy
  rcases Finset.mem_val.mp hy with hy'
  rcases Finset.mem_image.mp hy' with ⟨i, _hi, rfl⟩
  exact (hpos i).trans_le (hx i).1.1

/-- Strict-sign certificate version of `all_roots_positive_of_left_pos`. -/
theorem StrictFinBracketCertificate.all_roots_positive_of_left_pos {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ p.roots, 0 < y := by
  exact cert.toFinBracketCertificate.all_roots_positive_of_left_pos hpos

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- If `z^2` is a positive real number, then `z` is real. -/
theorem complex_sq_eq_pos_real_im_eq_zero {z : ℂ} {x : ℝ}
    (hx : 0 < x)
    (hz : z ^ 2 = algebraMap ℝ ℂ x) :
    z.im = 0 := by
  have him : 2 * z.re * z.im = 0 := by
    have h := congrArg Complex.im hz
    simpa [sq, Complex.mul_im, mul_comm, mul_left_comm, mul_assoc] using h
  have hre : z.re ^ 2 - z.im ^ 2 = x := by
    have h := congrArg Complex.re hz
    simpa [sq, Complex.mul_re, pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  rcases mul_eq_zero.mp him with hre_factor | him0
  · exfalso
    have hre0 : z.re = 0 := by nlinarith
    have hx_nonpos : x ≤ 0 := by
      rw [← hre, hre0]
      nlinarith [sq_nonneg z.im]
    exact (not_le_of_gt hx) hx_nonpos
  · exact him0

/--
If every real root of a nonzero split real polynomial `p` is positive, then
all complex `w` satisfying `p(w^2) = 0` are real.
-/
theorem complex_square_root_im_eq_zero_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : (p.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0) :
    z.im = 0 := by
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hp
  have hzmem : z ^ 2 ∈ (p.map (algebraMap ℝ ℂ)).roots := by
    exact (Polynomial.mem_roots hpmap).mpr hz
  have hroots := roots_map_complex_eq_of_splits (p := p) hsplits
  rw [← hroots] at hzmem
  rcases Multiset.mem_map.mp hzmem with ⟨x, hxroot, hxz⟩
  exact complex_sq_eq_pos_real_im_eq_zero (hpos x hxroot) hxz.symm

/--
Composition form of `complex_square_root_im_eq_zero_of_splits_positive_roots`:
all complex roots of `p.comp (X^2)` are real when the roots of `p` are
positive real numbers.
-/
theorem complex_root_im_eq_zero_of_comp_X_sq_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  have hz' : (p.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0 := by
    simpa [Polynomial.map_comp, Polynomial.eval_comp] using hz
  exact complex_square_root_im_eq_zero_of_splits_positive_roots hsplits hp hpos hz'

/-- `w`-hyperbolicity endpoint for weak-sign finite bracket certificates. -/
theorem FinBracketCertificate.comp_X_sq_complex_root_im_eq_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  exact complex_root_im_eq_zero_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

/-- `w`-hyperbolicity endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.comp_X_sq_complex_root_im_eq_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 := by
  exact complex_root_im_eq_zero_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- The quadratic `X^2 - a` splits over `ℝ` when `a` is positive. -/
theorem splits_X_sq_sub_C_of_pos {a : ℝ} (ha : 0 < a) :
    ((X ^ 2 : ℝ[X]) - C a).Splits := by
  have hfactor : (X ^ 2 : ℝ[X]) - C a =
      (X - C (Real.sqrt a)) * (X + C (Real.sqrt a)) := by
    rw [show C a = C ((Real.sqrt a) ^ 2) by rw [Real.sq_sqrt ha.le]]
    simp [pow_two]
    ring
  rw [hfactor]
  exact (Splits.X_sub_C _).mul (Splits.X_add_C _)

/--
If a real polynomial splits and all its real roots are positive, then its
composition with `X^2` also splits over `ℝ`.
-/
theorem splits_comp_X_sq_of_splits_positive_roots {p : ℝ[X]}
    (hsplits : p.Splits)
    (hpos : ∀ y ∈ p.roots, 0 < y) :
    (p.comp (X ^ 2)).Splits := by
  classical
  have hp_eq := congrArg (fun q : ℝ[X] => q.comp (X ^ 2)) hsplits.eq_prod_roots
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp] at hp_eq
  rw [hp_eq]
  refine (Splits.C _).mul (Splits.multisetProd ?_)
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨linear, hlinear, rfl⟩
  rcases Multiset.mem_map.mp hlinear with ⟨y, hy, rfl⟩
  simpa [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.pow_comp]
    using splits_X_sq_sub_C_of_pos (hpos y hy)

/-- `w`-polynomial splitting endpoint for weak-sign finite bracket certificates. -/
theorem FinBracketCertificate.comp_X_sq_splits_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits := by
  exact splits_comp_X_sq_of_splits_positive_roots cert.splits
    (cert.all_roots_positive_of_left_pos hpos)

/-- `w`-polynomial splitting endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.comp_X_sq_splits_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits := by
  exact splits_comp_X_sq_of_splits_positive_roots cert.splits
    (cert.all_roots_positive_of_left_pos hpos)

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A complex number with zero imaginary part is the image of its real part. -/
theorem complex_is_real_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simp [hz]

/-- If `z^2` is a positive real number, then `z` is a real complex number. -/
theorem complex_sq_eq_pos_real_is_real {z : ℂ} {x : ℝ}
    (hx : 0 < x)
    (hz : z ^ 2 = algebraMap ℝ ℂ x) :
    ∃ y : ℝ, z = algebraMap ℝ ℂ y := by
  exact complex_is_real_of_im_eq_zero (complex_sq_eq_pos_real_im_eq_zero hx hz)

/-- Existential real-root form of `complex_square_root_im_eq_zero_of_splits_positive_roots`. -/
theorem complex_square_root_is_real_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : (p.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_is_real_of_im_eq_zero
    (complex_square_root_im_eq_zero_of_splits_positive_roots hsplits hp hpos hz)

/-- Existential real-root form for roots of `p.comp (X^2)`. -/
theorem complex_root_is_real_of_comp_X_sq_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_is_real_of_im_eq_zero
    (complex_root_im_eq_zero_of_comp_X_sq_of_splits_positive_roots hsplits hp hpos hz)

/-- `w`-root reality endpoint for weak-sign finite bracket certificates. -/
theorem FinBracketCertificate.comp_X_sq_complex_root_is_real_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_root_is_real_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

/-- `w`-root reality endpoint for strict-sign finite bracket certificates. -/
theorem StrictFinBracketCertificate.comp_X_sq_complex_root_is_real_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    ∃ x : ℝ, z = algebraMap ℝ ℂ x := by
  exact complex_root_is_real_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Composing a nonzero polynomial with `X^2` stays nonzero. -/
theorem comp_X_sq_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    p.comp (X ^ 2) ≠ 0 := by
  intro hzero
  have h := (Polynomial.comp_eq_zero_iff.mp hzero)
  rcases h with hp0 | hconst
  · exact hp hp0
  · have hdeg : ((X ^ 2 : ℝ[X]).natDegree = 0) := by
      rw [hconst.2, Polynomial.natDegree_C]
    have hxdeg : ((X ^ 2 : ℝ[X]).natDegree = 2) := by
      simp
    omega

/-- Degree of the `X^2` composition, in the orientation useful for certificates. -/
theorem natDegree_comp_X_sq (p : ℝ[X]) :
    (p.comp (X ^ 2)).natDegree = p.natDegree * 2 := by
  rw [Polynomial.natDegree_comp]
  simp

/-- A degree-`d` bound for `p` gives a degree-`2*d` bound after `X^2` composition. -/
theorem natDegree_comp_X_sq_le {d : ℕ} {p : ℝ[X]}
    (hdegree : p.natDegree ≤ d) :
    (p.comp (X ^ 2)).natDegree ≤ 2 * d := by
  rw [natDegree_comp_X_sq]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.mul_le_mul_right 2 hdegree

/-- Complexifying a nonzero `X^2` composition stays nonzero. -/
theorem map_comp_X_sq_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    (p.comp (X ^ 2)).map (algebraMap ℝ ℂ) ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr
    (JensenLadder.Sturm.comp_X_sq_ne_zero hp)

/-- Nonzeroness endpoint for weak-sign finite bracket certificates after `X^2` composition. -/
theorem FinBracketCertificate.comp_X_sq_ne_zero {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.comp (X ^ 2) ≠ 0 := by
  exact JensenLadder.Sturm.comp_X_sq_ne_zero (p := p) cert.nonzero

/-- Degree endpoint for weak-sign finite bracket certificates after `X^2` composition. -/
theorem FinBracketCertificate.comp_X_sq_natDegree_le {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    (p.comp (X ^ 2)).natDegree ≤ 2 * d := by
  exact natDegree_comp_X_sq_le cert.degree_le

/-- Complexified nonzeroness endpoint for weak-sign certificates after `X^2` composition. -/
theorem FinBracketCertificate.map_comp_X_sq_ne_zero {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    (p.comp (X ^ 2)).map (algebraMap ℝ ℂ) ≠ 0 := by
  exact JensenLadder.Sturm.map_comp_X_sq_ne_zero (p := p) cert.nonzero

/-- Nonzeroness endpoint for strict-sign finite bracket certificates after `X^2` composition. -/
theorem StrictFinBracketCertificate.comp_X_sq_ne_zero {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.comp (X ^ 2) ≠ 0 := by
  exact JensenLadder.Sturm.comp_X_sq_ne_zero (p := p) cert.nonzero

/-- Degree endpoint for strict-sign finite bracket certificates after `X^2` composition. -/
theorem StrictFinBracketCertificate.comp_X_sq_natDegree_le {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    (p.comp (X ^ 2)).natDegree ≤ 2 * d := by
  exact natDegree_comp_X_sq_le cert.degree_le

/-- Complexified nonzeroness endpoint for strict-sign certificates after `X^2` composition. -/
theorem StrictFinBracketCertificate.map_comp_X_sq_ne_zero {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    (p.comp (X ^ 2)).map (algebraMap ℝ ℂ) ≠ 0 := by
  exact JensenLadder.Sturm.map_comp_X_sq_ne_zero (p := p) cert.nonzero

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- If `z^2` is a positive real number, then `z` is nonzero. -/
theorem complex_sq_eq_pos_real_ne_zero {z : ℂ} {x : ℝ}
    (hx : 0 < x)
    (hz : z ^ 2 = algebraMap ℝ ℂ x) :
    z ≠ 0 := by
  intro hz0
  have hx0c : algebraMap ℝ ℂ x = 0 := by
    rw [← hz, hz0]
    simp
  have hx0 : x = 0 := (FaithfulSMul.algebraMap_injective ℝ ℂ) hx0c
  exact hx.ne' hx0

/-- If roots of `p` are positive, then roots of `p(z^2)` are nonzero. -/
theorem complex_square_root_ne_zero_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : (p.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0) :
    z ≠ 0 := by
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hp
  have hzmem : z ^ 2 ∈ (p.map (algebraMap ℝ ℂ)).roots := by
    exact (Polynomial.mem_roots hpmap).mpr hz
  have hroots := roots_map_complex_eq_of_splits (p := p) hsplits
  rw [← hroots] at hzmem
  rcases Multiset.mem_map.mp hzmem with ⟨x, hxroot, hxz⟩
  exact complex_sq_eq_pos_real_ne_zero (hpos x hxroot) hxz.symm

/-- Composition form: roots of `p.comp (X^2)` are nonzero when roots of `p` are positive. -/
theorem complex_root_ne_zero_of_comp_X_sq_of_splits_positive_roots {p : ℝ[X]} {z : ℂ}
    (hsplits : p.Splits)
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z ≠ 0 := by
  have hz' : (p.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0 := by
    simpa [Polynomial.map_comp, Polynomial.eval_comp] using hz
  exact complex_square_root_ne_zero_of_splits_positive_roots hsplits hp hpos hz'

/-- Nonzero-root endpoint for weak-sign finite bracket certificates after `X^2` composition. -/
theorem FinBracketCertificate.comp_X_sq_complex_root_ne_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z ≠ 0 := by
  exact complex_root_ne_zero_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

/-- Nonzero-root endpoint for strict-sign finite bracket certificates after `X^2` composition. -/
theorem StrictFinBracketCertificate.comp_X_sq_complex_root_ne_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i)
    {z : ℂ}
    (hz : ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0) :
    z ≠ 0 := by
  exact complex_root_ne_zero_of_comp_X_sq_of_splits_positive_roots cert.splits cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hz

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A full `Fin d` bracket certificate fills the degree exactly. -/
theorem FinBracketCertificate.natDegree_eq {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.natDegree = d := by
  classical
  rcases cert.exists_roots_eq with ⟨x, _hx, hxpair, hroots⟩
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact hxpair hne hij
  let S : Finset ℝ := Finset.univ.image x
  have hrootcardS : p.roots.card = S.card := by
    rw [hroots]
    exact (Finset.card_def S).symm
  have hScard : S.card = d := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ]
    simp
  have hrootcard : p.roots.card = d := by
    rw [hrootcardS, hScard]
  have hroot_le_nat : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hd_le : d ≤ p.natDegree := by
    simpa [hrootcard] using hroot_le_nat
  exact le_antisymm cert.degree_le hd_le

/-- Strict-sign certificate version of exact degree filling. -/
theorem StrictFinBracketCertificate.natDegree_eq {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.natDegree = d := by
  exact cert.toFinBracketCertificate.natDegree_eq

/-- Exact degree of the `X^2` lift for a full weak-sign certificate. -/
theorem FinBracketCertificate.comp_X_sq_natDegree_eq {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    (p.comp (X ^ 2)).natDegree = 2 * d := by
  rw [natDegree_comp_X_sq, cert.natDegree_eq, Nat.mul_comm]

/-- Exact degree of the `X^2` lift for a full strict-sign certificate. -/
theorem StrictFinBracketCertificate.comp_X_sq_natDegree_eq {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    (p.comp (X ^ 2)).natDegree = 2 * d := by
  rw [natDegree_comp_X_sq, cert.natDegree_eq, Nat.mul_comm]

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A full weak-sign certificate has exactly `d` roots counted with multiplicity. -/
theorem FinBracketCertificate.roots_card_eq {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.roots.card = d := by
  calc
    p.roots.card = p.natDegree := cert.splits.natDegree_eq_card_roots.symm
    _ = d := cert.natDegree_eq

/-- A full strict-sign certificate has exactly `d` roots counted with multiplicity. -/
theorem StrictFinBracketCertificate.roots_card_eq {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.roots.card = d := by
  exact cert.toFinBracketCertificate.roots_card_eq

/-- The `X^2` lift has exactly `2*d` roots counted with multiplicity. -/
theorem FinBracketCertificate.comp_X_sq_roots_card_eq_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.card = 2 * d := by
  calc
    (p.comp (X ^ 2)).roots.card = (p.comp (X ^ 2)).natDegree :=
      (cert.comp_X_sq_splits_of_left_pos hpos).natDegree_eq_card_roots.symm
    _ = 2 * d := cert.comp_X_sq_natDegree_eq

/-- Strict-sign certificate version of the lifted root count endpoint. -/
theorem StrictFinBracketCertificate.comp_X_sq_roots_card_eq_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.card = 2 * d := by
  calc
    (p.comp (X ^ 2)).roots.card = (p.comp (X ^ 2)).natDegree :=
      (cert.comp_X_sq_splits_of_left_pos hpos).natDegree_eq_card_roots.symm
    _ = 2 * d := cert.comp_X_sq_natDegree_eq

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Summary endpoint for certified positive roots of the base `X`-polynomial. -/
theorem FinBracketCertificate.positive_roots_summary {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    p.Splits ∧
      p.natDegree = d ∧
      p.roots.card = d ∧
      (∀ y ∈ p.roots, 0 < y) := by
  exact ⟨cert.splits, cert.natDegree_eq, cert.roots_card_eq,
    cert.all_roots_positive_of_left_pos hpos⟩

/-- Strict-sign version of the base positive-root summary endpoint. -/
theorem StrictFinBracketCertificate.positive_roots_summary {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    p.Splits ∧
      p.natDegree = d ∧
      p.roots.card = d ∧
      (∀ y ∈ p.roots, 0 < y) := by
  exact cert.toFinBracketCertificate.positive_roots_summary hpos

/-- Summary endpoint for the even `w`-polynomial lift `p.comp (X^2)`. -/
theorem FinBracketCertificate.comp_X_sq_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

/-- Strict-sign version of the even `w`-polynomial summary endpoint. -/
theorem StrictFinBracketCertificate.comp_X_sq_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Positive roots exclude zero from the root multiset. -/
theorem zero_not_mem_roots_of_positive_roots {p : ℝ[X]}
    (hpos : ∀ y ∈ p.roots, 0 < y) :
    (0 : ℝ) ∉ p.roots := by
  intro hzero
  exact (lt_irrefl (0 : ℝ)) (hpos 0 hzero)

/-- If all roots of a nonzero real polynomial are positive, its value at zero is nonzero. -/
theorem eval_zero_ne_zero_of_positive_roots {p : ℝ[X]}
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y) :
    p.eval 0 ≠ 0 := by
  intro hzero
  have hmem : (0 : ℝ) ∈ p.roots := (Polynomial.mem_roots hp).mpr hzero
  exact zero_not_mem_roots_of_positive_roots hpos hmem

/-- The `X^2` lift of a positive-root polynomial is nonzero at zero. -/
theorem comp_X_sq_eval_zero_ne_zero_of_splits_positive_roots {p : ℝ[X]}
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y) :
    (p.comp (X ^ 2)).eval 0 ≠ 0 := by
  have hp0 := eval_zero_ne_zero_of_positive_roots hp hpos
  simpa [Polynomial.eval_comp] using hp0

/-- Real roots of the `X^2` lift are nonzero. -/
theorem real_root_ne_zero_of_comp_X_sq_of_splits_positive_roots {p : ℝ[X]} {y : ℝ}
    (hp : p ≠ 0)
    (hpos : ∀ y ∈ p.roots, 0 < y)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    y ≠ 0 := by
  intro hy0
  have hq : p.comp (X ^ 2) ≠ 0 := comp_X_sq_ne_zero hp
  have hyeval : (p.comp (X ^ 2)).eval y = 0 := (Polynomial.mem_roots hq).mp hy
  have h0eval : (p.comp (X ^ 2)).eval 0 = 0 := by
    simpa [hy0] using hyeval
  exact comp_X_sq_eval_zero_ne_zero_of_splits_positive_roots hp hpos h0eval

/-- Real-root nonzero endpoint for weak-sign finite certificates after `X^2` composition. -/
theorem FinBracketCertificate.comp_X_sq_real_roots_ne_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots, y ≠ 0 := by
  intro y hy
  exact real_root_ne_zero_of_comp_X_sq_of_splits_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

/-- Real-root nonzero endpoint for strict-sign finite certificates after `X^2` composition. -/
theorem StrictFinBracketCertificate.comp_X_sq_real_roots_ne_zero_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots, y ≠ 0 := by
  intro y hy
  exact real_root_ne_zero_of_comp_X_sq_of_splits_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Full summary endpoint for the even `w`-polynomial lift `p.comp (X^2)`. -/
theorem FinBracketCertificate.comp_X_sq_full_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots, y ≠ 0) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_roots_ne_zero_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

/-- Strict-sign version of the full even `w`-polynomial summary endpoint. -/
theorem StrictFinBracketCertificate.comp_X_sq_full_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots, y ≠ 0) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_roots_ne_zero_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A real root of `p.comp (X^2)` maps back to a root of `p` after squaring. -/
theorem square_mem_roots_of_comp_X_sq_root {p : ℝ[X]} {y : ℝ}
    (hp : p ≠ 0)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    y ^ 2 ∈ p.roots := by
  have hq : p.comp (X ^ 2) ≠ 0 := comp_X_sq_ne_zero hp
  have hyeval : (p.comp (X ^ 2)).eval y = 0 := (Polynomial.mem_roots hq).mp hy
  have hp_eval : p.eval (y ^ 2) = 0 := by
    simpa [Polynomial.eval_comp] using hyeval
  exact (Polynomial.mem_roots hp).mpr hp_eval

/-- If the roots of `p` are positive, a lifted real root has positive square. -/
theorem square_pos_of_comp_X_sq_root_of_positive_roots {p : ℝ[X]} {y : ℝ}
    (hp : p ≠ 0)
    (hpos : ∀ x ∈ p.roots, 0 < x)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    0 < y ^ 2 := by
  exact hpos (y ^ 2) (square_mem_roots_of_comp_X_sq_root hp hy)

/-- Weak-sign certificate wrapper for the root-square pullback. -/
theorem FinBracketCertificate.comp_X_sq_root_square_mem_roots
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    y ^ 2 ∈ p.roots := by
  exact square_mem_roots_of_comp_X_sq_root cert.nonzero hy

/-- Strict-sign certificate wrapper for the root-square pullback. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_square_mem_roots
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    y ^ 2 ∈ p.roots := by
  exact square_mem_roots_of_comp_X_sq_root cert.nonzero hy

/-- Weak-sign certificate wrapper: lifted real roots have positive square. -/
theorem FinBracketCertificate.comp_X_sq_root_square_pos_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots, 0 < y ^ 2 := by
  intro y hy
  exact square_pos_of_comp_X_sq_root_of_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

/-- Strict-sign certificate wrapper: lifted real roots have positive square. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_square_pos_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots, 0 < y ^ 2 := by
  intro y hy
  exact square_pos_of_comp_X_sq_root_of_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Bundled real-root facts for the `X^2` lift of a weak-sign certificate. -/
theorem FinBracketCertificate.comp_X_sq_real_root_square_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots,
      y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2 := by
  intro y hy
  exact ⟨cert.comp_X_sq_real_roots_ne_zero_of_left_pos hpos y hy,
    cert.comp_X_sq_root_square_mem_roots hy,
    cert.comp_X_sq_root_square_pos_of_left_pos hpos y hy⟩

/-- Bundled real-root facts for the `X^2` lift of a strict-sign certificate. -/
theorem StrictFinBracketCertificate.comp_X_sq_real_root_square_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots,
      y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2 := by
  intro y hy
  exact ⟨cert.comp_X_sq_real_roots_ne_zero_of_left_pos hpos y hy,
    cert.comp_X_sq_root_square_mem_roots hy,
    cert.comp_X_sq_root_square_pos_of_left_pos hpos y hy⟩

/-- Full summary for the even lift, including the square pullback for real roots. -/
theorem FinBracketCertificate.comp_X_sq_full_square_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_root_square_summary_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

/-- Strict-sign full summary for the even lift, including the square pullback for real roots. -/
theorem StrictFinBracketCertificate.comp_X_sq_full_square_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_root_square_summary_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A nonnegative root of `p` lifts to the positive square-root root of `p.comp (X^2)`. -/
theorem sqrt_mem_roots_comp_X_sq_of_mem_roots {p : ℝ[X]} {x : ℝ}
    (hp : p ≠ 0)
    (hxnonneg : 0 ≤ x)
    (hx : x ∈ p.roots) :
    Real.sqrt x ∈ (p.comp (X ^ 2)).roots := by
  have hq : p.comp (X ^ 2) ≠ 0 := comp_X_sq_ne_zero hp
  have hxeval : p.eval x = 0 := (Polynomial.mem_roots hp).mp hx
  have hqeval : (p.comp (X ^ 2)).eval (Real.sqrt x) = 0 := by
    simpa [Polynomial.eval_comp, Real.sq_sqrt hxnonneg] using hxeval
  exact (Polynomial.mem_roots hq).mpr hqeval

/-- A nonnegative root of `p` lifts to the negative square-root root of `p.comp (X^2)`. -/
theorem neg_sqrt_mem_roots_comp_X_sq_of_mem_roots {p : ℝ[X]} {x : ℝ}
    (hp : p ≠ 0)
    (hxnonneg : 0 ≤ x)
    (hx : x ∈ p.roots) :
    -Real.sqrt x ∈ (p.comp (X ^ 2)).roots := by
  have hq : p.comp (X ^ 2) ≠ 0 := comp_X_sq_ne_zero hp
  have hxeval : p.eval x = 0 := (Polynomial.mem_roots hp).mp hx
  have hsq : (-Real.sqrt x) ^ 2 = x := by
    simpa using (Real.sq_sqrt hxnonneg)
  have hqeval : (p.comp (X ^ 2)).eval (-Real.sqrt x) = 0 := by
    simpa [Polynomial.eval_comp, hsq] using hxeval
  exact (Polynomial.mem_roots hq).mpr hqeval

/-- A positive real has distinct positive and negative square roots. -/
theorem sqrt_ne_neg_sqrt_of_pos {x : ℝ} (hx : 0 < x) :
    Real.sqrt x ≠ -Real.sqrt x := by
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsnonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  intro h
  rw [h] at hspos
  linarith

/-- A positive root of `p` lifts to two distinct real roots of `p.comp (X^2)`. -/
theorem sqrt_pair_mem_roots_comp_X_sq_of_pos_root {p : ℝ[X]} {x : ℝ}
    (hp : p ≠ 0)
    (hxpos : 0 < x)
    (hx : x ∈ p.roots) :
    Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
      -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
      Real.sqrt x ≠ -Real.sqrt x := by
  exact ⟨sqrt_mem_roots_comp_X_sq_of_mem_roots hp hxpos.le hx,
    neg_sqrt_mem_roots_comp_X_sq_of_mem_roots hp hxpos.le hx,
    sqrt_ne_neg_sqrt_of_pos hxpos⟩

/-- Weak-sign certificate wrapper: every base root lifts to its two square-root roots. -/
theorem FinBracketCertificate.comp_X_sq_sqrt_pair_mem_roots_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ x ∈ p.roots,
      Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
        -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
        Real.sqrt x ≠ -Real.sqrt x := by
  intro x hx
  exact sqrt_pair_mem_roots_comp_X_sq_of_pos_root cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos x hx) hx

/-- Strict-sign certificate wrapper: every base root lifts to its two square-root roots. -/
theorem StrictFinBracketCertificate.comp_X_sq_sqrt_pair_mem_roots_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ x ∈ p.roots,
      Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
        -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
        Real.sqrt x ≠ -Real.sqrt x := by
  intro x hx
  exact sqrt_pair_mem_roots_comp_X_sq_of_pos_root cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos x hx) hx

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Two-way real-root correspondence for the `X^2` lift of a weak-sign certificate. -/
theorem FinBracketCertificate.comp_X_sq_root_correspondence_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (∀ y ∈ (p.comp (X ^ 2)).roots,
      y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) := by
  exact ⟨cert.comp_X_sq_real_root_square_summary_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos⟩

/-- Two-way real-root correspondence for the `X^2` lift of a strict-sign certificate. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_correspondence_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (∀ y ∈ (p.comp (X ^ 2)).roots,
      y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) := by
  exact ⟨cert.comp_X_sq_real_root_square_summary_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos⟩

/-- Full weak-sign summary with the two-way real-root correspondence included. -/
theorem FinBracketCertificate.comp_X_sq_full_correspondence_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_root_square_summary_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

/-- Full strict-sign summary with the two-way real-root correspondence included. -/
theorem StrictFinBracketCertificate.comp_X_sq_full_correspondence_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        y ≠ 0 ∧ y ^ 2 ∈ p.roots ∧ 0 < y ^ 2) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_real_root_square_summary_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A lifted real root is one of the two square roots of a positive base root. -/
theorem comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_positive_roots
    {p : ℝ[X]} {y : ℝ}
    (hp : p ≠ 0)
    (hpos : ∀ x ∈ p.roots, 0 < x)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ x ∈ p.roots, 0 < x ∧ (y = Real.sqrt x ∨ y = -Real.sqrt x) := by
  have hy2mem : y ^ 2 ∈ p.roots := square_mem_roots_of_comp_X_sq_root hp hy
  refine ⟨y ^ 2, hy2mem, hpos (y ^ 2) hy2mem, ?_⟩
  by_cases hynonneg : 0 ≤ y
  · left
    exact (Real.sqrt_sq hynonneg).symm
  · right
    have hyneg : y < 0 := lt_of_not_ge hynonneg
    have hsqrt : Real.sqrt (y ^ 2) = -y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hyneg]
    linarith

/-- Weak-sign certificate wrapper: every lifted real root is `±sqrt` of a base root. -/
theorem FinBracketCertificate.comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots,
      ∃ x ∈ p.roots, 0 < x ∧ (y = Real.sqrt x ∨ y = -Real.sqrt x) := by
  intro y hy
  exact comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

/-- Strict-sign certificate wrapper: every lifted real root is `±sqrt` of a base root. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ y ∈ (p.comp (X ^ 2)).roots,
      ∃ x ∈ p.roots, 0 < x ∧ (y = Real.sqrt x ∨ y = -Real.sqrt x) := by
  intro y hy
  exact comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_positive_roots cert.nonzero
    (cert.all_roots_positive_of_left_pos hpos) hy

/-- Full weak-sign summary with an existential `±sqrt` characterization of lifted real roots. -/
theorem FinBracketCertificate.comp_X_sq_full_characterization_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        ∃ x ∈ p.roots, 0 < x ∧ (y = Real.sqrt x ∨ y = -Real.sqrt x)) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

/-- Full strict-sign summary with an existential `±sqrt` characterization of lifted real roots. -/
theorem StrictFinBracketCertificate.comp_X_sq_full_characterization_summary_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits ∧
      (p.comp (X ^ 2)).natDegree = 2 * d ∧
      (p.comp (X ^ 2)).roots.card = 2 * d ∧
      (∀ y ∈ (p.comp (X ^ 2)).roots,
        ∃ x ∈ p.roots, 0 < x ∧ (y = Real.sqrt x ∨ y = -Real.sqrt x)) ∧
      (∀ x ∈ p.roots,
        Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          -Real.sqrt x ∈ (p.comp (X ^ 2)).roots ∧
          Real.sqrt x ≠ -Real.sqrt x) ∧
      (∀ z : ℂ,
        ((p.comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 →
          (∃ x : ℝ, z = algebraMap ℝ ℂ x) ∧ z ≠ 0) := by
  refine ⟨cert.comp_X_sq_splits_of_left_pos hpos, cert.comp_X_sq_natDegree_eq,
    cert.comp_X_sq_roots_card_eq_of_left_pos hpos,
    cert.comp_X_sq_root_exists_base_sqrt_or_neg_sqrt_of_left_pos hpos,
    cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos, ?_⟩
  intro z hz
  exact ⟨cert.comp_X_sq_complex_root_is_real_of_left_pos hpos hz,
    cert.comp_X_sq_complex_root_ne_zero_of_left_pos hpos hz⟩

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Square roots are injective on nonnegative reals. -/
theorem eq_of_sqrt_eq_sqrt_of_nonneg {x y : ℝ}
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (h : Real.sqrt x = Real.sqrt y) :
    x = y := by
  have hsq := congrArg (fun t : ℝ => t ^ 2) h
  simpa [Real.sq_sqrt hx, Real.sq_sqrt hy] using hsq

/-- Positive square roots cannot be negatives of positive square roots. -/
theorem sqrt_ne_neg_sqrt_of_pos_pos {x y : ℝ}
    (hx : 0 < x)
    (hy : 0 < y) :
    Real.sqrt x ≠ -Real.sqrt y := by
  have hxroot : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hyroot : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  intro h
  have hxlt : Real.sqrt x < 0 := by
    rw [h]
    linarith
  exact (not_lt_of_ge (Real.sqrt_nonneg x)) hxlt

/-- Distinct positive base roots have four pairwise separated square-root lifts. -/
theorem sqrt_lift_pair_disjoint_of_pos_ne {x y : ℝ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy : x ≠ y) :
    Real.sqrt x ≠ Real.sqrt y ∧
      Real.sqrt x ≠ -Real.sqrt y ∧
      -Real.sqrt x ≠ Real.sqrt y ∧
      -Real.sqrt x ≠ -Real.sqrt y := by
  refine ⟨?_, sqrt_ne_neg_sqrt_of_pos_pos hx hy, ?_, ?_⟩
  · intro h
    exact hxy (eq_of_sqrt_eq_sqrt_of_nonneg hx.le hy.le h)
  · intro h
    have h' : Real.sqrt y = -Real.sqrt x := by
      linarith
    exact sqrt_ne_neg_sqrt_of_pos_pos hy hx h'
  · intro h
    have h' : Real.sqrt x = Real.sqrt y := by
      linarith
    exact hxy (eq_of_sqrt_eq_sqrt_of_nonneg hx.le hy.le h')

/-- Weak-sign certificate wrapper: distinct base roots give disjoint square-root lift pairs. -/
theorem FinBracketCertificate.comp_X_sq_sqrt_lift_pair_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ x ∈ p.roots, ∀ y ∈ p.roots, x ≠ y →
      Real.sqrt x ≠ Real.sqrt y ∧
        Real.sqrt x ≠ -Real.sqrt y ∧
        -Real.sqrt x ≠ Real.sqrt y ∧
        -Real.sqrt x ≠ -Real.sqrt y := by
  intro x hx y hy hxy
  exact sqrt_lift_pair_disjoint_of_pos_ne
    (cert.all_roots_positive_of_left_pos hpos x hx)
    (cert.all_roots_positive_of_left_pos hpos y hy)
    hxy

/-- Strict-sign certificate wrapper: distinct base roots give disjoint square-root lift pairs. -/
theorem StrictFinBracketCertificate.comp_X_sq_sqrt_lift_pair_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ x ∈ p.roots, ∀ y ∈ p.roots, x ≠ y →
      Real.sqrt x ≠ Real.sqrt y ∧
        Real.sqrt x ≠ -Real.sqrt y ∧
        -Real.sqrt x ≠ Real.sqrt y ∧
        -Real.sqrt x ≠ -Real.sqrt y := by
  intro x hx y hy hxy
  exact sqrt_lift_pair_disjoint_of_pos_ne
    (cert.all_roots_positive_of_left_pos hpos x hx)
    (cert.all_roots_positive_of_left_pos hpos y hy)
    hxy

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- A degree-filling bracket certificate gives a root multiset with no duplicates. -/
theorem FinBracketCertificate.roots_nodup {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.roots.Nodup := by
  classical
  rcases cert.exists_roots_eq with ⟨x, _hx, _hxpair, hroots⟩
  let S : Finset ℝ := Finset.univ.image x
  rw [hroots]
  exact S.nodup

/-- Strict-sign certificate version of root-multiset no-duplicates. -/
theorem StrictFinBracketCertificate.roots_nodup {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.roots.Nodup := by
  exact cert.toFinBracketCertificate.roots_nodup

/-- A weak-sign certificate has exactly `d` distinct real roots. -/
theorem FinBracketCertificate.roots_toFinset_card_eq {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    p.roots.toFinset.card = d := by
  rw [Multiset.toFinset_card_of_nodup cert.roots_nodup]
  exact cert.roots_card_eq

/-- A strict-sign certificate has exactly `d` distinct real roots. -/
theorem StrictFinBracketCertificate.roots_toFinset_card_eq {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    p.roots.toFinset.card = d := by
  exact cert.toFinBracketCertificate.roots_toFinset_card_eq

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- The `X^2` lift of a positive-root certificate has no duplicate roots. -/
theorem FinBracketCertificate.comp_X_sq_roots_nodup_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.Nodup := by
  classical
  let A : Finset ℝ := p.roots.toFinset.image Real.sqrt
  let B : Finset ℝ := p.roots.toFinset.image (fun x : ℝ => -Real.sqrt x)
  let T : Finset ℝ := A ∪ B
  have hroot_pos : ∀ x ∈ p.roots, 0 < x := cert.all_roots_positive_of_left_pos hpos
  have hinjA : Set.InjOn Real.sqrt (↑p.roots.toFinset) := by
    intro x hx y hy hxy
    have hxroot : x ∈ p.roots := by simpa using hx
    have hyroot : y ∈ p.roots := by simpa using hy
    exact eq_of_sqrt_eq_sqrt_of_nonneg (hroot_pos x hxroot).le (hroot_pos y hyroot).le hxy
  have hinjB : Set.InjOn (fun x : ℝ => -Real.sqrt x) (↑p.roots.toFinset) := by
    intro x hx y hy hxy
    have hxroot : x ∈ p.roots := by simpa using hx
    have hyroot : y ∈ p.roots := by simpa using hy
    have hsqrt : Real.sqrt x = Real.sqrt y := by linarith
    exact eq_of_sqrt_eq_sqrt_of_nonneg (hroot_pos x hxroot).le (hroot_pos y hyroot).le hsqrt
  have hAcard : A.card = d := by
    dsimp [A]
    rw [Finset.card_image_of_injOn hinjA, cert.roots_toFinset_card_eq]
  have hBcard : B.card = d := by
    dsimp [B]
    rw [Finset.card_image_of_injOn hinjB, cert.roots_toFinset_card_eq]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rcases Finset.mem_image.mp hzA with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hzB with ⟨y, hy, hzy⟩
    have hxroot : x ∈ p.roots := by simpa using hx
    have hyroot : y ∈ p.roots := by simpa using hy
    exact sqrt_ne_neg_sqrt_of_pos_pos (hroot_pos x hxroot) (hroot_pos y hyroot) hzy.symm
  have hTcard : T.card = 2 * d := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard, two_mul]
  have hTroots : ∀ y ∈ T, (p.comp (X ^ 2)).eval y = 0 := by
    intro y hy
    rw [Finset.mem_union] at hy
    cases hy with
    | inl hyA =>
        rcases Finset.mem_image.mp hyA with ⟨x, hx, rfl⟩
        have hxroot : x ∈ p.roots := by simpa using hx
        have hmem := (cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos x hxroot).1
        exact (Polynomial.mem_roots (cert.comp_X_sq_ne_zero)).mp hmem
    | inr hyB =>
        rcases Finset.mem_image.mp hyB with ⟨x, hx, hxy⟩
        have hxroot : x ∈ p.roots := by simpa using hx
        have hmem := (cert.comp_X_sq_sqrt_pair_mem_roots_of_left_pos hpos x hxroot).2.1
        have hmem' : y ∈ (p.comp (X ^ 2)).roots := by
          simpa [← hxy] using hmem
        exact (Polynomial.mem_roots (cert.comp_X_sq_ne_zero)).mp hmem'
  have hdegree : (p.comp (X ^ 2)).natDegree ≤ T.card := by
    rw [hTcard, cert.comp_X_sq_natDegree_eq]
  have hroots : (p.comp (X ^ 2)).roots = T.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hTroots hdegree cert.comp_X_sq_ne_zero
  rw [hroots]
  exact T.nodup

/-- Strict-sign certificate version of lifted root-multiset no-duplicates. -/
theorem StrictFinBracketCertificate.comp_X_sq_roots_nodup_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.Nodup := by
  exact cert.toFinBracketCertificate.comp_X_sq_roots_nodup_of_left_pos hpos

/-- The `X^2` lift has exactly `2*d` distinct roots. -/
theorem FinBracketCertificate.comp_X_sq_roots_toFinset_card_eq_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.toFinset.card = 2 * d := by
  rw [Multiset.toFinset_card_of_nodup (cert.comp_X_sq_roots_nodup_of_left_pos hpos)]
  exact cert.comp_X_sq_roots_card_eq_of_left_pos hpos

/-- Strict-sign certificate version: the `X^2` lift has exactly `2*d` distinct roots. -/
theorem StrictFinBracketCertificate.comp_X_sq_roots_toFinset_card_eq_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).roots.toFinset.card = 2 * d := by
  exact cert.toFinBracketCertificate.comp_X_sq_roots_toFinset_card_eq_of_left_pos hpos

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Two certificate brackets cannot contain the same point unless their indices agree. -/
theorem FinBracketCertificate.bracket_index_unique {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {i j : Fin d} {y : ℝ}
    (hyi : y ∈ Icc (cert.L i) (cert.R i))
    (hyj : y ∈ Icc (cert.L j) (cert.R j)) :
    j = i := by
  by_contra hne
  exact (Set.disjoint_left.mp (cert.disjoint hne) hyj hyi)

/-- Strict-sign certificate version of bracket-index uniqueness. -/
theorem StrictFinBracketCertificate.bracket_index_unique {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {i j : Fin d} {y : ℝ}
    (hyi : y ∈ Icc (cert.L i) (cert.R i))
    (hyj : y ∈ Icc (cert.L j) (cert.R j)) :
    j = i := by
  exact cert.toFinBracketCertificate.bracket_index_unique hyi hyj

/-- Every root of a degree-filling bracket certificate lies in one certificate bracket. -/
theorem FinBracketCertificate.exists_bracket_of_mem_roots {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ p.roots) :
    ∃ i : Fin d, y ∈ Icc (cert.L i) (cert.R i) := by
  classical
  rcases cert.exists_roots_eq with ⟨x, hx, _hxpair, hroots⟩
  have hyS : y ∈ (Finset.univ.image x : Finset ℝ) := by
    rw [hroots] at hy
    simpa [Finset.mem_def] using hy
  rcases Finset.mem_image.mp hyS with ⟨i, _hi, hxy⟩
  refine ⟨i, ?_⟩
  rw [← hxy]
  exact (hx i).1

/-- Strict-sign certificate version: every root lies in one certificate bracket. -/
theorem StrictFinBracketCertificate.exists_bracket_of_mem_roots {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ p.roots) :
    ∃ i : Fin d, y ∈ Icc (cert.L i) (cert.R i) := by
  exact cert.toFinBracketCertificate.exists_bracket_of_mem_roots hy

/-- Every root of a degree-filling bracket certificate lies in a unique certificate bracket. -/
theorem FinBracketCertificate.exists_unique_bracket_of_mem_roots {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ p.roots) :
    ∃! i : Fin d, y ∈ Icc (cert.L i) (cert.R i) := by
  rcases cert.exists_bracket_of_mem_roots hy with ⟨i, hyi⟩
  refine ⟨i, hyi, ?_⟩
  intro j hyj
  exact cert.bracket_index_unique hyi hyj

/-- Strict-sign certificate version: every root lies in a unique certificate bracket. -/
theorem StrictFinBracketCertificate.exists_unique_bracket_of_mem_roots {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ p.roots) :
    ∃! i : Fin d, y ∈ Icc (cert.L i) (cert.R i) := by
  exact cert.toFinBracketCertificate.exists_unique_bracket_of_mem_roots hy

/-- A real root of the `X^2` lift has its square in a unique base certificate bracket. -/
theorem FinBracketCertificate.comp_X_sq_root_square_exists_unique_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃! i : Fin d, y ^ 2 ∈ Icc (cert.L i) (cert.R i) := by
  exact cert.exists_unique_bracket_of_mem_roots
    (square_mem_roots_of_comp_X_sq_root cert.nonzero hy)

/-- Strict-sign version: a lifted real root square lies in a unique base certificate bracket. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_square_exists_unique_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃! i : Fin d, y ^ 2 ∈ Icc (cert.L i) (cert.R i) := by
  exact cert.toFinBracketCertificate.comp_X_sq_root_square_exists_unique_bracket hy

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- If `y^2` lies in a base bracket, then `|y|` lies in the square-root bracket. -/
theorem abs_mem_sqrt_Icc_of_sq_mem_Icc {L R y : ℝ}
    (hy : y ^ 2 ∈ Icc L R) :
    |y| ∈ Icc (Real.sqrt L) (Real.sqrt R) := by
  constructor
  · calc
      Real.sqrt L ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hy.1
      _ = |y| := Real.sqrt_sq_eq_abs y
  · calc
      |y| = Real.sqrt (y ^ 2) := (Real.sqrt_sq_eq_abs y).symm
      _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hy.2

/-- Nonnegative signed version of `abs_mem_sqrt_Icc_of_sq_mem_Icc`. -/
theorem mem_sqrt_Icc_of_nonneg_sq_mem_Icc {L R y : ℝ}
    (hynonneg : 0 ≤ y)
    (hy : y ^ 2 ∈ Icc L R) :
    y ∈ Icc (Real.sqrt L) (Real.sqrt R) := by
  simpa [abs_of_nonneg hynonneg] using abs_mem_sqrt_Icc_of_sq_mem_Icc hy

/-- Nonpositive signed version of `abs_mem_sqrt_Icc_of_sq_mem_Icc`. -/
theorem mem_neg_sqrt_Icc_of_nonpos_sq_mem_Icc {L R y : ℝ}
    (hynonpos : y ≤ 0)
    (hy : y ^ 2 ∈ Icc L R) :
    y ∈ Icc (-Real.sqrt R) (-Real.sqrt L) := by
  have h := abs_mem_sqrt_Icc_of_sq_mem_Icc hy
  constructor
  · have hle : -Real.sqrt R ≤ -|y| := neg_le_neg h.2
    simpa [abs_of_nonpos hynonpos] using hle
  · have hle : -|y| ≤ -Real.sqrt L := neg_le_neg h.1
    simpa [abs_of_nonpos hynonpos] using hle

/-- A lifted real root has absolute value in the square-root of a base certificate bracket. -/
theorem FinBracketCertificate.comp_X_sq_root_abs_exists_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, |y| ∈ Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  rcases cert.comp_X_sq_root_square_exists_unique_bracket hy with ⟨i, hyi, _huniq⟩
  exact ⟨i, abs_mem_sqrt_Icc_of_sq_mem_Icc hyi⟩

/-- Strict-sign version: lifted root absolute values lie in square-root base brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_root_abs_exists_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, |y| ∈ Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_root_abs_exists_sqrt_bracket hy

/-- Nonnegative lifted roots lie in a positive square-root certificate bracket. -/
theorem FinBracketCertificate.comp_X_sq_nonneg_root_exists_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hynonneg : 0 ≤ y)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, y ∈ Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  rcases cert.comp_X_sq_root_square_exists_unique_bracket hy with ⟨i, hyi, _huniq⟩
  exact ⟨i, mem_sqrt_Icc_of_nonneg_sq_mem_Icc hynonneg hyi⟩

/-- Strict-sign version: nonnegative lifted roots lie in positive square-root brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_nonneg_root_exists_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hynonneg : 0 ≤ y)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, y ∈ Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_nonneg_root_exists_sqrt_bracket hynonneg hy

/-- Nonpositive lifted roots lie in a negative square-root certificate bracket. -/
theorem FinBracketCertificate.comp_X_sq_nonpos_root_exists_neg_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) {y : ℝ}
    (hynonpos : y ≤ 0)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, y ∈ Icc (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)) := by
  rcases cert.comp_X_sq_root_square_exists_unique_bracket hy with ⟨i, hyi, _huniq⟩
  exact ⟨i, mem_neg_sqrt_Icc_of_nonpos_sq_mem_Icc hynonpos hyi⟩

/-- Strict-sign version: nonpositive lifted roots lie in negative square-root brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_nonpos_root_exists_neg_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) {y : ℝ}
    (hynonpos : y ≤ 0)
    (hy : y ∈ (p.comp (X ^ 2)).roots) :
    ∃ i : Fin d, y ∈ Icc (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_nonpos_root_exists_neg_sqrt_bracket hynonpos hy

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Evaluation of the `X^2` lift at a nonnegative square root. -/
theorem eval_comp_X_sq_sqrt {p : ℝ[X]} {x : ℝ}
    (hx : 0 ≤ x) :
    (p.comp (X ^ 2)).eval (Real.sqrt x) = p.eval x := by
  simp [Polynomial.eval_comp, Real.sq_sqrt hx]

/-- Evaluation of the `X^2` lift at a negative square root. -/
theorem eval_comp_X_sq_neg_sqrt {p : ℝ[X]} {x : ℝ}
    (hx : 0 ≤ x) :
    (p.comp (X ^ 2)).eval (-Real.sqrt x) = p.eval x := by
  have hsq : (-Real.sqrt x) ^ 2 = x := by
    simpa using (Real.sq_sqrt hx)
  simp [Polynomial.eval_comp, hsq]

/-- Base sign-change rows transfer to the positive square-root bracket. -/
theorem hasSignChangeOn_comp_X_sq_sqrt {p : ℝ[X]} {L R : ℝ}
    (hL : 0 ≤ L)
    (hR : 0 ≤ R)
    (hsign : HasSignChangeOn (fun t : ℝ => p.eval t) L R) :
    HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (Real.sqrt L) (Real.sqrt R) := by
  rcases hsign with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨by simpa [eval_comp_X_sq_sqrt (p := p) hL] using hleft,
      by simpa [eval_comp_X_sq_sqrt (p := p) hR] using hright⟩
  · exact Or.inr ⟨by simpa [eval_comp_X_sq_sqrt (p := p) hL] using hleft,
      by simpa [eval_comp_X_sq_sqrt (p := p) hR] using hright⟩

/-- Base sign-change rows transfer to the negative square-root bracket. -/
theorem hasSignChangeOn_comp_X_sq_neg_sqrt {p : ℝ[X]} {L R : ℝ}
    (hL : 0 ≤ L)
    (hR : 0 ≤ R)
    (hsign : HasSignChangeOn (fun t : ℝ => p.eval t) L R) :
    HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (-Real.sqrt R) (-Real.sqrt L) := by
  rcases hsign with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inr ⟨by simpa [eval_comp_X_sq_neg_sqrt (p := p) hR] using hright,
      by simpa [eval_comp_X_sq_neg_sqrt (p := p) hL] using hleft⟩
  · exact Or.inl ⟨by simpa [eval_comp_X_sq_neg_sqrt (p := p) hR] using hright,
      by simpa [eval_comp_X_sq_neg_sqrt (p := p) hL] using hleft⟩

/-- Square-root bracket order from base bracket order. -/
theorem sqrt_bracket_order {L R : ℝ} (hLR : L ≤ R) :
    Real.sqrt L ≤ Real.sqrt R :=
  Real.sqrt_le_sqrt hLR

/-- Negative square-root bracket order from base bracket order. -/
theorem neg_sqrt_bracket_order {L R : ℝ} (hLR : L ≤ R) :
    -Real.sqrt R ≤ -Real.sqrt L :=
  neg_le_neg (Real.sqrt_le_sqrt hLR)

/-- Weak-sign certificate: each row transfers to the positive square-root bracket. -/
theorem FinBracketCertificate.comp_X_sq_pos_sqrt_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  intro i
  have hL : 0 ≤ cert.L i := (hpos i).le
  have hR : 0 ≤ cert.R i := le_trans hL (cert.bracket i)
  exact hasSignChangeOn_comp_X_sq_sqrt hL hR (cert.sign i)

/-- Weak-sign certificate: each row transfers to the negative square-root bracket. -/
theorem FinBracketCertificate.comp_X_sq_neg_sqrt_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)) := by
  intro i
  have hL : 0 ≤ cert.L i := (hpos i).le
  have hR : 0 ≤ cert.R i := le_trans hL (cert.bracket i)
  exact hasSignChangeOn_comp_X_sq_neg_sqrt hL hR (cert.sign i)

/-- Weak-sign certificate: positive square-root brackets are ordered. -/
theorem FinBracketCertificate.comp_X_sq_pos_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∀ i, Real.sqrt (cert.L i) ≤ Real.sqrt (cert.R i) := by
  intro i
  exact sqrt_bracket_order (cert.bracket i)

/-- Weak-sign certificate: negative square-root brackets are ordered. -/
theorem FinBracketCertificate.comp_X_sq_neg_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∀ i, -Real.sqrt (cert.R i) ≤ -Real.sqrt (cert.L i) := by
  intro i
  exact neg_sqrt_bracket_order (cert.bracket i)

/-- Strict-sign certificate: each row transfers to the positive square-root bracket. -/
theorem StrictFinBracketCertificate.comp_X_sq_pos_sqrt_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_pos_sqrt_sign_of_left_pos hpos

/-- Strict-sign certificate: each row transfers to the negative square-root bracket. -/
theorem StrictFinBracketCertificate.comp_X_sq_neg_sqrt_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_neg_sqrt_sign_of_left_pos hpos

/-- Strict-sign certificate: positive square-root brackets are ordered. -/
theorem StrictFinBracketCertificate.comp_X_sq_pos_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∀ i, Real.sqrt (cert.L i) ≤ Real.sqrt (cert.R i) := by
  exact cert.toFinBracketCertificate.comp_X_sq_pos_sqrt_bracket

/-- Strict-sign certificate: negative square-root brackets are ordered. -/
theorem StrictFinBracketCertificate.comp_X_sq_neg_sqrt_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∀ i, -Real.sqrt (cert.R i) ≤ -Real.sqrt (cert.L i) := by
  exact cert.toFinBracketCertificate.comp_X_sq_neg_sqrt_bracket

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

/-- Points in a square-root bracket square back into the base bracket. -/
theorem sq_mem_Icc_of_mem_sqrt_Icc {L R y : ℝ}
    (hR : 0 ≤ R)
    (hy : y ∈ Icc (Real.sqrt L) (Real.sqrt R)) :
    y ^ 2 ∈ Icc L R := by
  have hynonneg : 0 ≤ y := le_trans (Real.sqrt_nonneg L) hy.1
  constructor
  · have hsqrt : Real.sqrt L ≤ Real.sqrt (y ^ 2) := by
      simpa [Real.sqrt_sq hynonneg] using hy.1
    exact (Real.sqrt_le_sqrt_iff (sq_nonneg y)).mp hsqrt
  · have hsqrt : Real.sqrt (y ^ 2) ≤ Real.sqrt R := by
      simpa [Real.sqrt_sq hynonneg] using hy.2
    exact (Real.sqrt_le_sqrt_iff hR).mp hsqrt

/-- Points in a negative square-root bracket square back into the base bracket. -/
theorem sq_mem_Icc_of_mem_neg_sqrt_Icc {L R y : ℝ}
    (hR : 0 ≤ R)
    (hy : y ∈ Icc (-Real.sqrt R) (-Real.sqrt L)) :
    y ^ 2 ∈ Icc L R := by
  have hneg : -y ∈ Icc (Real.sqrt L) (Real.sqrt R) := by
    constructor
    · have h := neg_le_neg hy.2
      simpa using h
    · have h := neg_le_neg hy.1
      simpa using h
  have hsq := sq_mem_Icc_of_mem_sqrt_Icc hR hneg
  simpa [sq] using hsq

/-- Positive square-root brackets inherit base disjointness. -/
theorem disjoint_sqrt_Icc_of_disjoint_Icc {L₁ R₁ L₂ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂)
    (hdisj : Disjoint (Icc L₁ R₁) (Icc L₂ R₂)) :
    Disjoint (Icc (Real.sqrt L₁) (Real.sqrt R₁))
      (Icc (Real.sqrt L₂) (Real.sqrt R₂)) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  exact (Set.disjoint_left.mp hdisj)
    (sq_mem_Icc_of_mem_sqrt_Icc hR₁ hy1)
    (sq_mem_Icc_of_mem_sqrt_Icc hR₂ hy2)

/-- Negative square-root brackets inherit base disjointness. -/
theorem disjoint_neg_sqrt_Icc_of_disjoint_Icc {L₁ R₁ L₂ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂)
    (hdisj : Disjoint (Icc L₁ R₁) (Icc L₂ R₂)) :
    Disjoint (Icc (-Real.sqrt R₁) (-Real.sqrt L₁))
      (Icc (-Real.sqrt R₂) (-Real.sqrt L₂)) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  exact (Set.disjoint_left.mp hdisj)
    (sq_mem_Icc_of_mem_neg_sqrt_Icc hR₁ hy1)
    (sq_mem_Icc_of_mem_neg_sqrt_Icc hR₂ hy2)

/-- Positive and negative square-root brackets are separated when both base left endpoints are positive. -/
theorem disjoint_sqrt_Icc_neg_sqrt_Icc_of_left_pos {L₁ R₁ L₂ R₂ : ℝ}
    (hL₁ : 0 < L₁)
    (hL₂ : 0 < L₂) :
    Disjoint (Icc (Real.sqrt L₁) (Real.sqrt R₁))
      (Icc (-Real.sqrt R₂) (-Real.sqrt L₂)) := by
  rw [Set.disjoint_left]
  intro y hypos hyneg
  have hpos : 0 < y := lt_of_lt_of_le (Real.sqrt_pos.2 hL₁) hypos.1
  have hsqrt₂ : 0 < Real.sqrt L₂ := Real.sqrt_pos.2 hL₂
  have hneg_upper : y ≤ -Real.sqrt L₂ := hyneg.2
  have hneg_bound : -Real.sqrt L₂ < 0 := by linarith
  have hlt : y < 0 := lt_of_le_of_lt hneg_upper hneg_bound
  exact (not_lt_of_ge hpos.le) hlt

/-- Certificate-level positive square-root bracket disjointness. -/
theorem FinBracketCertificate.comp_X_sq_pos_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)))
      (Icc (Real.sqrt (cert.L j)) (Real.sqrt (cert.R j))) := by
  intro i j hij
  have hRi : 0 ≤ cert.R i := le_trans (hpos i).le (cert.bracket i)
  have hRj : 0 ≤ cert.R j := le_trans (hpos j).le (cert.bracket j)
  exact disjoint_sqrt_Icc_of_disjoint_Icc hRi hRj (cert.disjoint hij)

/-- Certificate-level negative square-root bracket disjointness. -/
theorem FinBracketCertificate.comp_X_sq_neg_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)))
      (Icc (-Real.sqrt (cert.R j)) (-Real.sqrt (cert.L j))) := by
  intro i j hij
  have hRi : 0 ≤ cert.R i := le_trans (hpos i).le (cert.bracket i)
  have hRj : 0 ≤ cert.R j := le_trans (hpos j).le (cert.bracket j)
  exact disjoint_neg_sqrt_Icc_of_disjoint_Icc hRi hRj (cert.disjoint hij)

/-- Certificate-level separation between positive and negative square-root brackets. -/
theorem FinBracketCertificate.comp_X_sq_pos_neg_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i j, Disjoint
      (Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)))
      (Icc (-Real.sqrt (cert.R j)) (-Real.sqrt (cert.L j))) := by
  intro i j
  exact disjoint_sqrt_Icc_neg_sqrt_Icc_of_left_pos (hpos i) (hpos j)

/-- Strict-sign certificate positive square-root bracket disjointness. -/
theorem StrictFinBracketCertificate.comp_X_sq_pos_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)))
      (Icc (Real.sqrt (cert.L j)) (Real.sqrt (cert.R j))) := by
  exact cert.toFinBracketCertificate.comp_X_sq_pos_sqrt_disjoint_of_left_pos hpos

/-- Strict-sign certificate negative square-root bracket disjointness. -/
theorem StrictFinBracketCertificate.comp_X_sq_neg_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)))
      (Icc (-Real.sqrt (cert.R j)) (-Real.sqrt (cert.L j))) := by
  exact cert.toFinBracketCertificate.comp_X_sq_neg_sqrt_disjoint_of_left_pos hpos

/-- Strict-sign certificate separation between positive and negative square-root brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_pos_neg_sqrt_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i j, Disjoint
      (Icc (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)))
      (Icc (-Real.sqrt (cert.R j)) (-Real.sqrt (cert.L j))) := by
  exact cert.toFinBracketCertificate.comp_X_sq_pos_neg_sqrt_disjoint_of_left_pos hpos

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

noncomputable section

/-- Left endpoints for the sum-indexed lifted `X^2` bracket table. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_L {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin d ⊕ Fin d → ℝ
  | Sum.inl i => Real.sqrt (cert.L i)
  | Sum.inr i => -Real.sqrt (cert.R i)

/-- Right endpoints for the sum-indexed lifted `X^2` bracket table. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_R {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin d ⊕ Fin d → ℝ
  | Sum.inl i => Real.sqrt (cert.R i)
  | Sum.inr i => -Real.sqrt (cert.L i)

/-- Left endpoints for the strict-sign sum-indexed lifted `X^2` bracket table. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_L {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin d ⊕ Fin d → ℝ :=
  cert.toFinBracketCertificate.comp_X_sq_lifted_L

/-- Right endpoints for the strict-sign sum-indexed lifted `X^2` bracket table. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_R {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin d ⊕ Fin d → ℝ :=
  cert.toFinBracketCertificate.comp_X_sq_lifted_R

/-- The sum-indexed lifted table has ordered brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∀ a, cert.comp_X_sq_lifted_L a ≤ cert.comp_X_sq_lifted_R a := by
  intro a
  cases a with
  | inl i => exact cert.comp_X_sq_pos_sqrt_bracket i
  | inr i => exact cert.comp_X_sq_neg_sqrt_bracket i

/-- The strict-sign sum-indexed lifted table has ordered brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∀ a, cert.comp_X_sq_lifted_L a ≤ cert.comp_X_sq_lifted_R a := by
  exact cert.toFinBracketCertificate.comp_X_sq_lifted_bracket

/-- The sum-indexed lifted table has sign-change rows. -/
theorem FinBracketCertificate.comp_X_sq_lifted_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ a, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a) := by
  intro a
  cases a with
  | inl i => exact cert.comp_X_sq_pos_sqrt_sign_of_left_pos hpos i
  | inr i => exact cert.comp_X_sq_neg_sqrt_sign_of_left_pos hpos i

/-- The strict-sign sum-indexed lifted table has sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ a, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a) := by
  exact cert.toFinBracketCertificate.comp_X_sq_lifted_sign_of_left_pos hpos

/-- The sum-indexed lifted table has pairwise-disjoint brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun a b => Disjoint
      (Icc (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a))
      (Icc (cert.comp_X_sq_lifted_L b) (cert.comp_X_sq_lifted_R b)) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hab (by cases h; rfl)
          exact cert.comp_X_sq_pos_sqrt_disjoint_of_left_pos hpos hij
      | inr j =>
          exact cert.comp_X_sq_pos_neg_sqrt_disjoint_of_left_pos hpos i j
  | inr i =>
      cases b with
      | inl j =>
          exact (cert.comp_X_sq_pos_neg_sqrt_disjoint_of_left_pos hpos j i).symm
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hab (by cases h; rfl)
          exact cert.comp_X_sq_neg_sqrt_disjoint_of_left_pos hpos hij

/-- The strict-sign sum-indexed lifted table has pairwise-disjoint brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun a b => Disjoint
      (Icc (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a))
      (Icc (cert.comp_X_sq_lifted_L b) (cert.comp_X_sq_lifted_R b)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_lifted_disjoint_of_left_pos hpos

/-- Packaged sum-indexed lifted bracket table for `p.comp (X^2)`. -/
theorem FinBracketCertificate.comp_X_sq_lifted_table_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (Pairwise fun a b => Disjoint
      (Icc (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a))
      (Icc (cert.comp_X_sq_lifted_L b) (cert.comp_X_sq_lifted_R b))) ∧
      (∀ a, cert.comp_X_sq_lifted_L a ≤ cert.comp_X_sq_lifted_R a) ∧
      (∀ a, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
        (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a)) := by
  exact ⟨cert.comp_X_sq_lifted_disjoint_of_left_pos hpos,
    cert.comp_X_sq_lifted_bracket,
    cert.comp_X_sq_lifted_sign_of_left_pos hpos⟩

/-- Packaged strict-sign sum-indexed lifted bracket table for `p.comp (X^2)`. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_table_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (Pairwise fun a b => Disjoint
      (Icc (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a))
      (Icc (cert.comp_X_sq_lifted_L b) (cert.comp_X_sq_lifted_R b))) ∧
      (∀ a, cert.comp_X_sq_lifted_L a ≤ cert.comp_X_sq_lifted_R a) ∧
      (∀ a, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
        (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a)) := by
  exact cert.toFinBracketCertificate.comp_X_sq_lifted_table_of_left_pos hpos

/-- The sum-indexed lifted table is itself sufficient to prove splitting. -/
theorem FinBracketCertificate.comp_X_sq_splits_of_lifted_table_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits := by
  have hdegree : (p.comp (X ^ 2)).natDegree ≤ Fintype.card (Fin d ⊕ Fin d) := by
    rw [cert.comp_X_sq_natDegree_eq, Fintype.card_sum]
    simp [Nat.two_mul]
  exact splits_of_sign_changes
    (cert.comp_X_sq_lifted_disjoint_of_left_pos hpos)
    cert.comp_X_sq_lifted_bracket
    (fun _a => (p.comp (X ^ 2)).continuousOn)
    (cert.comp_X_sq_lifted_sign_of_left_pos hpos)
    cert.comp_X_sq_ne_zero hdegree

/-- Strict-sign version: the sum-indexed lifted table is sufficient to prove splitting. -/
theorem StrictFinBracketCertificate.comp_X_sq_splits_of_lifted_table_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    (p.comp (X ^ 2)).Splits := by
  exact cert.toFinBracketCertificate.comp_X_sq_splits_of_lifted_table_of_left_pos hpos

end

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

noncomputable section

/-- `Fin (d+d)` left endpoints for the lifted `X^2` bracket certificate. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_fin_L {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin (d + d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_L (finSumFinEquiv.symm i)

/-- `Fin (d+d)` right endpoints for the lifted `X^2` bracket certificate. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_fin_R {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin (d + d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_R (finSumFinEquiv.symm i)

/-- `Fin (d+d)` left endpoints for the strict lifted `X^2` bracket certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_fin_L {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin (d + d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_L (finSumFinEquiv.symm i)

/-- `Fin (d+d)` right endpoints for the strict lifted `X^2` bracket certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_fin_R {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin (d + d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_R (finSumFinEquiv.symm i)

/-- The `Fin (d+d)` lifted table has ordered brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_fin_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∀ i, cert.comp_X_sq_lifted_fin_L i ≤ cert.comp_X_sq_lifted_fin_R i := by
  intro i
  exact cert.comp_X_sq_lifted_bracket (finSumFinEquiv.symm i)

/-- The strict `Fin (d+d)` lifted table has ordered brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∀ i, cert.comp_X_sq_lifted_fin_L i ≤ cert.comp_X_sq_lifted_fin_R i := by
  intro i
  exact cert.comp_X_sq_lifted_bracket (finSumFinEquiv.symm i)

/-- The `Fin (d+d)` lifted table has sign-change rows. -/
theorem FinBracketCertificate.comp_X_sq_lifted_fin_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_fin_L i) (cert.comp_X_sq_lifted_fin_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_sign_of_left_pos hpos (finSumFinEquiv.symm i)

/-- The strict `Fin (d+d)` lifted table has weak sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_fin_L i) (cert.comp_X_sq_lifted_fin_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_sign_of_left_pos hpos (finSumFinEquiv.symm i)

/-- The `Fin (d+d)` lifted table has pairwise-disjoint brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_fin_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (cert.comp_X_sq_lifted_fin_L i) (cert.comp_X_sq_lifted_fin_R i))
      (Icc (cert.comp_X_sq_lifted_fin_L j) (cert.comp_X_sq_lifted_fin_R j)) := by
  intro i j hij
  have hsum : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j := by
    intro h
    exact hij (by
      have h' := congrArg (fun a => (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)) a) h
      simpa using h')
  exact cert.comp_X_sq_lifted_disjoint_of_left_pos hpos hsum

/-- The strict `Fin (d+d)` lifted table has pairwise-disjoint brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (cert.comp_X_sq_lifted_fin_L i) (cert.comp_X_sq_lifted_fin_R i))
      (Icc (cert.comp_X_sq_lifted_fin_L j) (cert.comp_X_sq_lifted_fin_R j)) := by
  intro i j hij
  have hsum : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j := by
    intro h
    exact hij (by
      have h' := congrArg (fun a => (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)) a) h
      simpa using h')
  exact cert.comp_X_sq_lifted_disjoint_of_left_pos hpos hsum

/-- Package a positive base certificate as a doubled `Fin (d+d)` certificate for `p.comp (X^2)`. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_finCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    FinBracketCertificate (d + d) (p.comp (X ^ 2)) where
  L := cert.comp_X_sq_lifted_fin_L
  R := cert.comp_X_sq_lifted_fin_R
  disjoint := cert.comp_X_sq_lifted_fin_disjoint_of_left_pos hpos
  bracket := cert.comp_X_sq_lifted_fin_bracket
  sign := cert.comp_X_sq_lifted_fin_sign_of_left_pos hpos
  nonzero := cert.comp_X_sq_ne_zero
  degree_le := by
    rw [cert.comp_X_sq_natDegree_eq, Nat.two_mul]

/-- Package a positive strict base certificate as a doubled weak `Fin (d+d)` certificate for `p.comp (X^2)`. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_finCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    FinBracketCertificate (d + d) (p.comp (X ^ 2)) :=
  cert.toFinBracketCertificate.comp_X_sq_lifted_finCertificate_of_left_pos hpos

/-- Strict base sign-change rows transfer to the positive square-root bracket. -/
theorem hasStrictSignChangeOn_comp_X_sq_sqrt {p : ℝ[X]} {L R : ℝ}
    (hL : 0 ≤ L)
    (hR : 0 ≤ R)
    (hsign : HasStrictSignChangeOn (fun t : ℝ => p.eval t) L R) :
    HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (Real.sqrt L) (Real.sqrt R) := by
  rcases hsign with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨by simpa [eval_comp_X_sq_sqrt (p := p) hL] using hleft,
      by simpa [eval_comp_X_sq_sqrt (p := p) hR] using hright⟩
  · exact Or.inr ⟨by simpa [eval_comp_X_sq_sqrt (p := p) hL] using hleft,
      by simpa [eval_comp_X_sq_sqrt (p := p) hR] using hright⟩

/-- Strict base sign-change rows transfer to the negative square-root bracket. -/
theorem hasStrictSignChangeOn_comp_X_sq_neg_sqrt {p : ℝ[X]} {L R : ℝ}
    (hL : 0 ≤ L)
    (hR : 0 ≤ R)
    (hsign : HasStrictSignChangeOn (fun t : ℝ => p.eval t) L R) :
    HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (-Real.sqrt R) (-Real.sqrt L) := by
  rcases hsign with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inr ⟨by simpa [eval_comp_X_sq_neg_sqrt (p := p) hR] using hright,
      by simpa [eval_comp_X_sq_neg_sqrt (p := p) hL] using hleft⟩
  · exact Or.inl ⟨by simpa [eval_comp_X_sq_neg_sqrt (p := p) hR] using hright,
      by simpa [eval_comp_X_sq_neg_sqrt (p := p) hL] using hleft⟩

/-- Strict-sign certificate: each row transfers strictly to the positive square-root bracket. -/
theorem StrictFinBracketCertificate.comp_X_sq_pos_sqrt_strict_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (Real.sqrt (cert.L i)) (Real.sqrt (cert.R i)) := by
  intro i
  have hL : 0 ≤ cert.L i := (hpos i).le
  have hR : 0 ≤ cert.R i := le_trans hL (cert.bracket i)
  exact hasStrictSignChangeOn_comp_X_sq_sqrt hL hR (cert.strict_sign i)

/-- Strict-sign certificate: each row transfers strictly to the negative square-root bracket. -/
theorem StrictFinBracketCertificate.comp_X_sq_neg_sqrt_strict_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (-Real.sqrt (cert.R i)) (-Real.sqrt (cert.L i)) := by
  intro i
  have hL : 0 ≤ cert.L i := (hpos i).le
  have hR : 0 ≤ cert.R i := le_trans hL (cert.bracket i)
  exact hasStrictSignChangeOn_comp_X_sq_neg_sqrt hL hR (cert.strict_sign i)

/-- The strict sum-indexed lifted table has strict sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_strict_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ a, HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_L a) (cert.comp_X_sq_lifted_R a) := by
  intro a
  cases a with
  | inl i => exact cert.comp_X_sq_pos_sqrt_strict_sign_of_left_pos hpos i
  | inr i => exact cert.comp_X_sq_neg_sqrt_strict_sign_of_left_pos hpos i

/-- The strict `Fin (d+d)` lifted table has strict sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_strict_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_fin_L i) (cert.comp_X_sq_lifted_fin_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_strict_sign_of_left_pos hpos (finSumFinEquiv.symm i)

/-- Package a positive strict base certificate as a doubled strict `Fin (d+d)` certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_finStrictCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    StrictFinBracketCertificate (d + d) (p.comp (X ^ 2)) where
  L := cert.comp_X_sq_lifted_fin_L
  R := cert.comp_X_sq_lifted_fin_R
  disjoint := cert.comp_X_sq_lifted_fin_disjoint_of_left_pos hpos
  bracket := cert.comp_X_sq_lifted_fin_bracket
  strict_sign := cert.comp_X_sq_lifted_fin_strict_sign_of_left_pos hpos
  nonzero := cert.comp_X_sq_ne_zero
  degree_le := by
    rw [cert.comp_X_sq_natDegree_eq, Nat.two_mul]

end

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Set Polynomial

noncomputable section

@[simp]
theorem FinBracketCertificate.comp_X_sq_lifted_fin_L_castAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_L (Fin.castAdd d i) = Real.sqrt (cert.L i) := by
  rw [FinBracketCertificate.comp_X_sq_lifted_fin_L]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp]
theorem FinBracketCertificate.comp_X_sq_lifted_fin_R_castAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_R (Fin.castAdd d i) = Real.sqrt (cert.R i) := by
  rw [FinBracketCertificate.comp_X_sq_lifted_fin_R]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp]
theorem FinBracketCertificate.comp_X_sq_lifted_fin_L_natAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_L (Fin.natAdd d i) = -Real.sqrt (cert.R i) := by
  rw [FinBracketCertificate.comp_X_sq_lifted_fin_L]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp]
theorem FinBracketCertificate.comp_X_sq_lifted_fin_R_natAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_R (Fin.natAdd d i) = -Real.sqrt (cert.L i) := by
  rw [FinBracketCertificate.comp_X_sq_lifted_fin_R]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp]
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_L_castAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_L (Fin.castAdd d i) = Real.sqrt (cert.L i) := by
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_fin_L]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_L]
  rfl

@[simp]
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_R_castAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_R (Fin.castAdd d i) = Real.sqrt (cert.R i) := by
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_fin_R]
  rw [finSumFinEquiv_symm_apply_castAdd]
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_R]
  rfl

@[simp]
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_L_natAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_L (Fin.natAdd d i) = -Real.sqrt (cert.R i) := by
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_fin_L]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_L]
  rfl

@[simp]
theorem StrictFinBracketCertificate.comp_X_sq_lifted_fin_R_natAdd
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) (i : Fin d) :
    cert.comp_X_sq_lifted_fin_R (Fin.natAdd d i) = -Real.sqrt (cert.L i) := by
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_fin_R]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rw [StrictFinBracketCertificate.comp_X_sq_lifted_R]
  rfl

/-- `Fin (2*d)` left endpoints for the lifted `X^2` bracket certificate. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_two_L {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin (2 * d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_fin_L ((finCongr (Nat.two_mul d)) i)

/-- `Fin (2*d)` right endpoints for the lifted `X^2` bracket certificate. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_two_R {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) : Fin (2 * d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_fin_R ((finCongr (Nat.two_mul d)) i)

/-- `Fin (2*d)` left endpoints for the strict lifted `X^2` bracket certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_two_L {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin (2 * d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_fin_L ((finCongr (Nat.two_mul d)) i)

/-- `Fin (2*d)` right endpoints for the strict lifted `X^2` bracket certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_two_R {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) : Fin (2 * d) → ℝ :=
  fun i => cert.comp_X_sq_lifted_fin_R ((finCongr (Nat.two_mul d)) i)

/-- The `Fin (2*d)` lifted table has ordered brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_two_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p) :
    ∀ i, cert.comp_X_sq_lifted_two_L i ≤ cert.comp_X_sq_lifted_two_R i := by
  intro i
  exact cert.comp_X_sq_lifted_fin_bracket ((finCongr (Nat.two_mul d)) i)

/-- The strict `Fin (2*d)` lifted table has ordered brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_two_bracket
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p) :
    ∀ i, cert.comp_X_sq_lifted_two_L i ≤ cert.comp_X_sq_lifted_two_R i := by
  intro i
  exact cert.comp_X_sq_lifted_fin_bracket ((finCongr (Nat.two_mul d)) i)

/-- The `Fin (2*d)` lifted table has sign-change rows. -/
theorem FinBracketCertificate.comp_X_sq_lifted_two_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_two_L i) (cert.comp_X_sq_lifted_two_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_fin_sign_of_left_pos hpos ((finCongr (Nat.two_mul d)) i)

/-- The strict `Fin (2*d)` lifted table has weak sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_two_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_two_L i) (cert.comp_X_sq_lifted_two_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_fin_sign_of_left_pos hpos ((finCongr (Nat.two_mul d)) i)

/-- The `Fin (2*d)` lifted table has pairwise-disjoint brackets. -/
theorem FinBracketCertificate.comp_X_sq_lifted_two_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (cert.comp_X_sq_lifted_two_L i) (cert.comp_X_sq_lifted_two_R i))
      (Icc (cert.comp_X_sq_lifted_two_L j) (cert.comp_X_sq_lifted_two_R j)) := by
  intro i j hij
  have hcast : (finCongr (Nat.two_mul d)) i ≠ (finCongr (Nat.two_mul d)) j := by
    intro h
    exact hij ((finCongr (Nat.two_mul d)).injective h)
  exact cert.comp_X_sq_lifted_fin_disjoint_of_left_pos hpos hcast

/-- The strict `Fin (2*d)` lifted table has pairwise-disjoint brackets. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_two_disjoint_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    Pairwise fun i j => Disjoint
      (Icc (cert.comp_X_sq_lifted_two_L i) (cert.comp_X_sq_lifted_two_R i))
      (Icc (cert.comp_X_sq_lifted_two_L j) (cert.comp_X_sq_lifted_two_R j)) := by
  intro i j hij
  have hcast : (finCongr (Nat.two_mul d)) i ≠ (finCongr (Nat.two_mul d)) j := by
    intro h
    exact hij ((finCongr (Nat.two_mul d)).injective h)
  exact cert.comp_X_sq_lifted_fin_disjoint_of_left_pos hpos hcast

/-- Package a positive base certificate as a doubled `Fin (2*d)` certificate for `p.comp (X^2)`. -/
noncomputable def FinBracketCertificate.comp_X_sq_lifted_twoCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : FinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    FinBracketCertificate (2 * d) (p.comp (X ^ 2)) where
  L := cert.comp_X_sq_lifted_two_L
  R := cert.comp_X_sq_lifted_two_R
  disjoint := cert.comp_X_sq_lifted_two_disjoint_of_left_pos hpos
  bracket := cert.comp_X_sq_lifted_two_bracket
  sign := cert.comp_X_sq_lifted_two_sign_of_left_pos hpos
  nonzero := cert.comp_X_sq_ne_zero
  degree_le := by
    rw [cert.comp_X_sq_natDegree_eq]

/-- Package a positive strict base certificate as a doubled weak `Fin (2*d)` certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_twoCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    FinBracketCertificate (2 * d) (p.comp (X ^ 2)) :=
  cert.toFinBracketCertificate.comp_X_sq_lifted_twoCertificate_of_left_pos hpos

/-- The strict `Fin (2*d)` lifted table has strict sign-change rows. -/
theorem StrictFinBracketCertificate.comp_X_sq_lifted_two_strict_sign_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    ∀ i, HasStrictSignChangeOn (fun t : ℝ => (p.comp (X ^ 2)).eval t)
      (cert.comp_X_sq_lifted_two_L i) (cert.comp_X_sq_lifted_two_R i) := by
  intro i
  exact cert.comp_X_sq_lifted_fin_strict_sign_of_left_pos hpos ((finCongr (Nat.two_mul d)) i)

/-- Package a positive strict base certificate as a doubled strict `Fin (2*d)` certificate. -/
noncomputable def StrictFinBracketCertificate.comp_X_sq_lifted_twoStrictCertificate_of_left_pos
    {d : ℕ} {p : ℝ[X]}
    (cert : StrictFinBracketCertificate d p)
    (hpos : ∀ i, 0 < cert.L i) :
    StrictFinBracketCertificate (2 * d) (p.comp (X ^ 2)) where
  L := cert.comp_X_sq_lifted_two_L
  R := cert.comp_X_sq_lifted_two_R
  disjoint := cert.comp_X_sq_lifted_two_disjoint_of_left_pos hpos
  bracket := cert.comp_X_sq_lifted_two_bracket
  strict_sign := cert.comp_X_sq_lifted_two_strict_sign_of_left_pos hpos
  nonzero := cert.comp_X_sq_ne_zero
  degree_le := by
    rw [cert.comp_X_sq_natDegree_eq]

end

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Polynomial
open Set

/-- Two closed intervals are disjoint when the first right endpoint is strictly left of the second left endpoint. -/
theorem disjoint_Icc_of_right_lt_left {a b c d : ℝ} (h : b < c) :
    Disjoint (Icc a b) (Icc c d) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact (lt_of_le_of_lt hx.2 h).not_ge hy.1

/-- Ordered endpoint rows induce pairwise-disjoint closed brackets. -/
theorem pairwise_disjoint_Icc_of_ordered_fin
    {d : ℕ} {L R : Fin d → ℝ}
    (hsep : ∀ ⦃i j : Fin d⦄, i < j → R i < L j) :
    Pairwise fun i j => Disjoint (Icc (L i) (R i)) (Icc (L j) (R j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact disjoint_Icc_of_right_lt_left (hsep hijlt)
  · exact (disjoint_Icc_of_right_lt_left (hsep hjilt)).symm

/--
Generator-facing certificate for positive, ordered, strict-sign endpoint rows.

The generator only supplies an ordered table: positive left endpoints, bracket
ordering, strict endpoint sign changes, nonzero, and degree bound. The generic
consumer derives pairwise disjointness and lowers to the existing Sturm
certificate API.
-/
structure PositiveOrderedStrictFinBracketCertificate (d : ℕ) (p : ℝ[X]) where
  L : Fin d → ℝ
  R : Fin d → ℝ
  left_pos : ∀ i, 0 < L i
  bracket : ∀ i, L i ≤ R i
  ordered : ∀ ⦃i j : Fin d⦄, i < j → R i < L j
  strict_sign : ∀ i, HasStrictSignChangeOn (fun t : ℝ => p.eval t) (L i) (R i)
  nonzero : p ≠ 0
  degree_le : p.natDegree ≤ d

/-- Lower an ordered strict endpoint table to the core strict bracket certificate. -/
def PositiveOrderedStrictFinBracketCertificate.toStrictFinBracketCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    StrictFinBracketCertificate d p where
  L := cert.L
  R := cert.R
  disjoint := pairwise_disjoint_Icc_of_ordered_fin cert.ordered
  bracket := cert.bracket
  strict_sign := cert.strict_sign
  nonzero := cert.nonzero
  degree_le := cert.degree_le

/-- Lower an ordered strict endpoint table to the weak bracket certificate. -/
def PositiveOrderedStrictFinBracketCertificate.toFinBracketCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    FinBracketCertificate d p :=
  cert.toStrictFinBracketCertificate.toFinBracketCertificate

/-- An ordered strict endpoint table proves that the polynomial splits over `ℝ`. -/
theorem PositiveOrderedStrictFinBracketCertificate.splits
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    p.Splits :=
  cert.toStrictFinBracketCertificate.splits

/-- A positive ordered table gives the doubled strict `Fin (2*d)` certificate for `p.comp (X^2)`. -/
noncomputable def PositiveOrderedStrictFinBracketCertificate.comp_X_sq_lifted_twoStrictCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    StrictFinBracketCertificate (2 * d) (p.comp (X ^ 2)) :=
  cert.toStrictFinBracketCertificate.comp_X_sq_lifted_twoStrictCertificate_of_left_pos cert.left_pos

/-- A positive ordered table gives the doubled weak `Fin (2*d)` certificate for `p.comp (X^2)`. -/
noncomputable def PositiveOrderedStrictFinBracketCertificate.comp_X_sq_lifted_twoCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    FinBracketCertificate (2 * d) (p.comp (X ^ 2)) :=
  cert.toStrictFinBracketCertificate.comp_X_sq_lifted_twoCertificate_of_left_pos cert.left_pos

/-- The doubled `X^2` polynomial from a positive ordered table splits over `ℝ`. -/
theorem PositiveOrderedStrictFinBracketCertificate.comp_X_sq_splits
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedStrictFinBracketCertificate d p) :
    (p.comp (X ^ 2)).Splits :=
  cert.comp_X_sq_lifted_twoStrictCertificate.splits

end Sturm
end JensenLadder

namespace JensenLadder
namespace Sturm

open Polynomial
open Set

/-- Sign target for Layer 1 endpoint rows: `pos` means `P(L) > 0 > P(R)`, `neg` means `P(L) < 0 < P(R)`. -/
inductive EndpointSignTarget where
  | pos
  | neg

namespace EndpointSignTarget

/-- Left endpoint inequality encoded by the sign target. -/
def leftSign (s : EndpointSignTarget) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  match s with
  | pos => 0 < f x
  | neg => f x < 0

/-- Right endpoint inequality encoded by the sign target. -/
def rightSign (s : EndpointSignTarget) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  match s with
  | pos => f x < 0
  | neg => 0 < f x

/-- Oriented endpoint inequalities imply the strict sign-change predicate. -/
theorem hasStrictSignChangeOn
    {s : EndpointSignTarget} {f : ℝ → ℝ} {a b : ℝ}
    (ha : s.leftSign f a)
    (hb : s.rightSign f b) :
    HasStrictSignChangeOn f a b := by
  cases s with
  | pos => exact Or.inr ⟨ha, hb⟩
  | neg => exact Or.inl ⟨ha, hb⟩

end EndpointSignTarget

/--
Generator-facing certificate for positive, ordered endpoint rows with explicit
Layer 1 sign targets.

For target `pos`, the row records `P(L_i) > 0` and `P(R_i) < 0`. For target
`neg`, it records `P(L_i) < 0` and `P(R_i) > 0`. This mirrors the skeleton
condition `s_i P(L_i) > 0`, `s_i P(R_i) < 0` while lowering to the existing
strict sign-change certificate API.
-/
structure PositiveOrderedOrientedFinBracketCertificate (d : ℕ) (p : ℝ[X]) where
  L : Fin d → ℝ
  R : Fin d → ℝ
  target : Fin d → EndpointSignTarget
  left_pos : ∀ i, 0 < L i
  bracket : ∀ i, L i ≤ R i
  ordered : ∀ ⦃i j : Fin d⦄, i < j → R i < L j
  left_sign : ∀ i, (target i).leftSign (fun t : ℝ => p.eval t) (L i)
  right_sign : ∀ i, (target i).rightSign (fun t : ℝ => p.eval t) (R i)
  nonzero : p ≠ 0
  degree_le : p.natDegree ≤ d

/-- Explicit endpoint targets produce strict sign-change rows. -/
theorem PositiveOrderedOrientedFinBracketCertificate.strict_sign
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    ∀ i, HasStrictSignChangeOn (fun t : ℝ => p.eval t) (cert.L i) (cert.R i) := by
  intro i
  exact EndpointSignTarget.hasStrictSignChangeOn (cert.left_sign i) (cert.right_sign i)

/-- Lower an oriented endpoint table to the positive ordered strict certificate. -/
def PositiveOrderedOrientedFinBracketCertificate.toPositiveOrderedStrictFinBracketCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    PositiveOrderedStrictFinBracketCertificate d p where
  L := cert.L
  R := cert.R
  left_pos := cert.left_pos
  bracket := cert.bracket
  ordered := cert.ordered
  strict_sign := cert.strict_sign
  nonzero := cert.nonzero
  degree_le := cert.degree_le

/-- Lower an oriented endpoint table to the core strict bracket certificate. -/
def PositiveOrderedOrientedFinBracketCertificate.toStrictFinBracketCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    StrictFinBracketCertificate d p :=
  cert.toPositiveOrderedStrictFinBracketCertificate.toStrictFinBracketCertificate

/-- Lower an oriented endpoint table to the weak bracket certificate. -/
def PositiveOrderedOrientedFinBracketCertificate.toFinBracketCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    FinBracketCertificate d p :=
  cert.toStrictFinBracketCertificate.toFinBracketCertificate

/-- An oriented endpoint table proves that the polynomial splits over `ℝ`. -/
theorem PositiveOrderedOrientedFinBracketCertificate.splits
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    p.Splits :=
  cert.toStrictFinBracketCertificate.splits

/-- An oriented endpoint table gives the doubled strict `Fin (2*d)` certificate for `p.comp (X^2)`. -/
noncomputable def PositiveOrderedOrientedFinBracketCertificate.comp_X_sq_lifted_twoStrictCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    StrictFinBracketCertificate (2 * d) (p.comp (X ^ 2)) :=
  cert.toPositiveOrderedStrictFinBracketCertificate.comp_X_sq_lifted_twoStrictCertificate

/-- An oriented endpoint table gives the doubled weak `Fin (2*d)` certificate for `p.comp (X^2)`. -/
noncomputable def PositiveOrderedOrientedFinBracketCertificate.comp_X_sq_lifted_twoCertificate
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    FinBracketCertificate (2 * d) (p.comp (X ^ 2)) :=
  cert.toPositiveOrderedStrictFinBracketCertificate.comp_X_sq_lifted_twoCertificate

/-- The doubled `X^2` polynomial from an oriented endpoint table splits over `ℝ`. -/
theorem PositiveOrderedOrientedFinBracketCertificate.comp_X_sq_splits
    {d : ℕ} {p : ℝ[X]}
    (cert : PositiveOrderedOrientedFinBracketCertificate d p) :
    (p.comp (X ^ 2)).Splits :=
  cert.comp_X_sq_lifted_twoStrictCertificate.splits

end Sturm
end JensenLadder
