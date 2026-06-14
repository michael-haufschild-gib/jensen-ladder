import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# T2 Airy/Langer edge consumer algebra

This module formalizes the deterministic certificate-consuming side of the T2
edge row from the Structure-Theorem route.  It proves that separated Airy-model
Wronskian remainder cells contain no actual Wronskian root, that same-sign model
value margins transfer to the actual pair, and that the normalized Wronskian
error expansion is the advertised finite algebraic identity.

The xi-specific work -- constructing the actual signed Langer coordinate,
choosing Airy cells, proving the interval inequalities, and deriving the
constants for consecutive xi-Jensen sections -- is not done here.

## Honest scope

This proves only the real-algebra and predicate-bookkeeping consumers for the
T2 edge row.  It is not a proof of T2 for the Riemann xi function, `CV(d)`,
global xi-Jensen hyperbolicity, or the Riemann Hypothesis.  Theorem M is proven,
but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace T2Edge

/-- The seven-term Wronskian-error budget from the A3'' edge note.  Producer
rows may prove `|Wact - WA| <= wronskianErrorBudget ...`; this module supplies
the algebraic consumers of that row. -/
def wronskianErrorBudget
    (D0 eps1 eps0p M1 eps0 M0 eps1p D1 L : ℝ) : ℝ :=
  D0 * eps1
    + eps0p * M1
    + eps0p * eps1
    + M0 * eps1p
    + eps0 * D1
    + eps0 * eps1p
    + L * (M0 + eps0) * (M1 + eps1)

/-- A separated Airy-model Wronskian cell cannot contain an actual Wronskian
root when the actual/model error is smaller than the model separation. -/
theorem wronskian_ne_zero_of_model_separation
    {Wact WA gamma eta : ℝ}
    (hWA : gamma ≤ |WA|)
    (herr : |Wact - WA| ≤ eta)
    (hgap : eta < gamma) :
    Wact ≠ 0 := by
  intro hzero
  have hWA_le_eta : |WA| ≤ eta := by
    calc
      |WA| = |Wact - WA| := by
        rw [hzero, zero_sub, abs_neg]
      _ ≤ eta := herr
  linarith

/-- Budget form of the separated-remainder-cell consumer. -/
theorem wronskian_ne_zero_of_error_budget
    {Wact WA gamma D0 eps1 eps0p M1 eps0 M0 eps1p D1 L : ℝ}
    (hWA : gamma ≤ |WA|)
    (herr :
      |Wact - WA| ≤
        wronskianErrorBudget D0 eps1 eps0p M1 eps0 M0 eps1p D1 L)
    (hbudget :
      wronskianErrorBudget D0 eps1 eps0p M1 eps0 M0 eps1p D1 L < gamma) :
    Wact ≠ 0 :=
  wronskian_ne_zero_of_model_separation hWA herr hbudget

/-- If both model values are positive with margins and the actual values are
closer than those margins, then the actual product is positive. -/
theorem product_pos_of_positive_model_margin
    {f0 f1 F0 F1 m0 m1 : ℝ}
    (_hm0 : 0 < m0)
    (_hm1 : 0 < m1)
    (hF0 : m0 ≤ F0)
    (hF1 : m1 ≤ F1)
    (hf0 : |f0 - F0| < m0)
    (hf1 : |f1 - F1| < m1) :
    0 < f0 * f1 := by
  have hf0_pos : 0 < f0 := by
    have hlow : -m0 < f0 - F0 := (abs_lt.mp hf0).1
    linarith
  have hf1_pos : 0 < f1 := by
    have hlow : -m1 < f1 - F1 := (abs_lt.mp hf1).1
    linarith
  exact mul_pos hf0_pos hf1_pos

/-- If both model values are negative with margins and the actual values are
closer than those margins, then the actual product is positive. -/
theorem product_pos_of_negative_model_margin
    {f0 f1 F0 F1 m0 m1 : ℝ}
    (_hm0 : 0 < m0)
    (_hm1 : 0 < m1)
    (hF0 : F0 ≤ -m0)
    (hF1 : F1 ≤ -m1)
    (hf0 : |f0 - F0| < m0)
    (hf1 : |f1 - F1| < m1) :
    0 < f0 * f1 := by
  have hf0_neg : f0 < 0 := by
    have hhigh : f0 - F0 < m0 := (abs_lt.mp hf0).2
    linarith
  have hf1_neg : f1 < 0 := by
    have hhigh : f1 - F1 < m1 := (abs_lt.mp hf1).2
    linarith
  exact mul_pos_of_neg_of_neg hf0_neg hf1_neg

/-- Signed version of the model-cell product row.  A common sign `sigma = 1` or
`sigma = -1` with strict value-error margins forces `f0 * f1 > 0`. -/
theorem product_pos_of_signed_model_margin
    {sigma f0 f1 F0 F1 m0 m1 : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hm0 : 0 < m0)
    (hm1 : 0 < m1)
    (hF0 : m0 ≤ sigma * F0)
    (hF1 : m1 ≤ sigma * F1)
    (hf0 : |f0 - F0| < m0)
    (hf1 : |f1 - F1| < m1) :
    0 < f0 * f1 := by
  rcases hsigma with rfl | rfl
  · norm_num at hF0 hF1
    exact product_pos_of_positive_model_margin hm0 hm1 hF0 hF1 hf0 hf1
  · norm_num at hF0 hF1
    have hF0_neg : F0 ≤ -m0 := by linarith
    have hF1_neg : F1 ≤ -m1 := by linarith
    exact product_pos_of_negative_model_margin hm0 hm1 hF0_neg hF1_neg hf0 hf1

/-- Positive prefactors transfer positivity of the normalized actual product to
positivity of the original consecutive-section product. -/
theorem product_pos_of_positive_prefactors
    {P0 P1 A0 A1 f0 f1 : ℝ}
    (hP0 : P0 = A0 * f0)
    (hP1 : P1 = A1 * f1)
    (hA0 : 0 < A0)
    (hA1 : 0 < A1)
    (hf : 0 < f0 * f1) :
    0 < P0 * P1 := by
  have hA : 0 < A0 * A1 := mul_pos hA0 hA1
  have hprod : 0 < (A0 * A1) * (f0 * f1) := mul_pos hA hf
  calc
    0 < (A0 * A1) * (f0 * f1) := hprod
    _ = P0 * P1 := by
      rw [hP0, hP1]
      ring

/-- Abstract A3' cover consumer.  If every edge root in the certified window is
either in a remainder cell that has no roots or in a model-root cell whose local
certificate is safe, then every edge root in the window is safe. -/
theorem edge_root_safe_of_cover
    {Point RCell CCell : Type*}
    {InWindow Root Safe : Point → Prop}
    {Remainder : RCell → Point → Prop}
    {ModelCell : CCell → Point → Prop}
    (hcover :
      ∀ x, InWindow x → (∃ r : RCell, Remainder r x) ∨
        ∃ c : CCell, ModelCell c x)
    (hrem : ∀ r x, Remainder r x → Root x → False)
    (hcell : ∀ c x, ModelCell c x → Root x → Safe x) :
    ∀ x, InWindow x → Root x → Safe x := by
  intro x hx hroot
  rcases hcover x hx with hRemainder | hModel
  · rcases hRemainder with ⟨r, hr⟩
    exact False.elim (hrem r x hr hroot)
  · rcases hModel with ⟨c, hc⟩
    exact hcell c x hc hroot

/-- Exact algebraic expansion of the normalized edge Wronskian error. -/
theorem wronskian_error_decomposition
    {F0 F1 F0p F1p e0 e1 e0p e1p Lambda Wact WA : ℝ}
    (hWact :
      Wact =
        (F0p + e0p) * (F1 + e1)
          - (F0 + e0) * (F1p + e1p)
          + Lambda * (F0 + e0) * (F1 + e1))
    (hWA : WA = F0p * F1 - F0 * F1p) :
    Wact - WA =
      F0p * e1 + e0p * F1 + e0p * e1
        - F0 * e1p - e0 * F1p - e0 * e1p
        + Lambda * (F0 + e0) * (F1 + e1) := by
  rw [hWact, hWA]
  ring

/-- Triangle-inequality consumer for the seven displayed Wronskian-error terms.
The term bounds are the certificate rows produced from the value, derivative,
and prefactor-drift envelopes. -/
theorem wronskian_error_le_of_term_bounds
    {Wact WA a b c d e f g
      D0 eps1 eps0p M1 eps0 M0 eps1p D1 L : ℝ}
    (hdecomp : Wact - WA = a + b + c - d - e - f + g)
    (ha : |a| ≤ D0 * eps1)
    (hb : |b| ≤ eps0p * M1)
    (hc : |c| ≤ eps0p * eps1)
    (hd : |d| ≤ M0 * eps1p)
    (he : |e| ≤ eps0 * D1)
    (hf : |f| ≤ eps0 * eps1p)
    (hg : |g| ≤ L * (M0 + eps0) * (M1 + eps1)) :
    |Wact - WA| ≤
      wronskianErrorBudget D0 eps1 eps0p M1 eps0 M0 eps1p D1 L := by
  have htri :
      |a + b + c - d - e - f + g| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    calc
      |a + b + c - d - e - f + g|
          = |a + b + c + (-d) + (-e) + (-f) + g| := by ring_nf
      _ ≤ |a + b + c + (-d) + (-e) + (-f)| + |g| := abs_add_le _ _
      _ ≤ |a + b + c + (-d) + (-e)| + |(-f)| + |g| := by
        linarith [abs_add_le (a + b + c + (-d) + (-e)) (-f)]
      _ ≤ |a + b + c + (-d)| + |(-e)| + |(-f)| + |g| := by
        linarith [abs_add_le (a + b + c + (-d)) (-e)]
      _ ≤ |a + b + c| + |(-d)| + |(-e)| + |(-f)| + |g| := by
        linarith [abs_add_le (a + b + c) (-d)]
      _ ≤ |a + b| + |c| + |(-d)| + |(-e)| + |(-f)| + |g| := by
        linarith [abs_add_le (a + b) c]
      _ ≤ |a| + |b| + |c| + |(-d)| + |(-e)| + |(-f)| + |g| := by
        linarith [abs_add_le a b]
      _ = |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
        rw [abs_neg, abs_neg, abs_neg]
  rw [hdecomp]
  calc
    |a + b + c - d - e - f + g|
        ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := htri
    _ ≤ wronskianErrorBudget D0 eps1 eps0p M1 eps0 M0 eps1p D1 L := by
      unfold wronskianErrorBudget
      linarith

end T2Edge
end JensenLadder
