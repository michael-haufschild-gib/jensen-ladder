import JensenLadder.AbsoluteBudgetFakeFamilyBlindness
import Mathlib.Tactic

/-!
# Adversarial sign-twist no-go

This module sharpens `AbsoluteBudgetFakeFamilyBlindness`: for any fixed test
vector, a unit sign twist can make every signed edge contribution point in the
negative direction simultaneously.

Thus a domination proof that is blind to signs/phases must be prepared to
dominate the absolute cross budget of the row.  This is a finite no-go for
sign-blind carrier arguments, not a statement about zeta zeros.  Theorem M is
proven, but Theorem M does not prove RH by itself.

Evidence class: formal/certificate artifact; dead-end elimination.
-/

namespace JensenLadder
namespace AdversarialSignTwistNoGo

open GlobalDominationReduction

namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/-- The scalar product contributed by one signed edge before the factor `2`. -/
def edgeProduct (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) : ℝ :=
  A.coupling e * v (A.left e) * v (A.right e)

/-- The vector-dependent absolute cross budget of the off-diagonal row. -/
def absoluteCrossBudget (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge, 2 * |edgeProduct A v e|

/--
The adversarial unit sign twist for a fixed vector: choose the sign that makes
`epsilon * edgeProduct` equal to `-|edgeProduct|`.
-/
noncomputable def worstTwist (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) : ℝ :=
  if 0 <= edgeProduct A v e then -1 else 1

omit [Fintype Edge] in
/-- The adversarial twist has unit absolute value edge by edge. -/
theorem abs_worstTwist
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    |worstTwist A v e| = 1 := by
  unfold worstTwist
  by_cases h : 0 <= edgeProduct A v e <;> simp [h]

omit [Fintype Edge] in
/-- The adversarial twist makes one edge product exactly negative absolute value. -/
theorem worstTwist_mul_edgeProduct_eq_neg_abs
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    worstTwist A v e * edgeProduct A v e = - |edgeProduct A v e| := by
  unfold worstTwist
  by_cases h : 0 <= edgeProduct A v e
  · simp [h, abs_of_nonneg h]
  · have hlt : edgeProduct A v e < 0 := lt_of_not_ge h
    simp [h, abs_of_neg hlt]

/--
After the adversarial unit twist, the signed off-diagonal row is exactly the
negative absolute cross budget.
-/
theorem offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v)).offDiagonalRow v
      = - absoluteCrossBudget A v := by
  calc
    (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v)).offDiagonalRow v
        = ∑ e : Edge, -(2 * |edgeProduct A v e|) := by
          unfold GlobalDominationReduction.SignedEdgeAssembly.offDiagonalRow
          apply Finset.sum_congr rfl
          intro e _he
          simp [AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist]
          calc
            2 * (worstTwist A v e * A.coupling e) * v (A.left e) * v (A.right e)
                = 2 * (worstTwist A v e * edgeProduct A v e) := by
                  unfold edgeProduct
                  ring
            _ = 2 * (- |edgeProduct A v e|) := by
                  rw [worstTwist_mul_edgeProduct_eq_neg_abs A v e]
            _ = -(2 * |edgeProduct A v e|) := by
                  ring
    _ = - absoluteCrossBudget A v := by
          unfold absoluteCrossBudget
          rw [Finset.sum_neg_distrib]

/--
The vector-dependent absolute cross budget is bounded by the usual edgewise
missing diagonal budget.
-/
theorem absoluteCrossBudget_le_missingDiagonalBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    absoluteCrossBudget A v <= A.missingDiagonalBudget v := by
  unfold absoluteCrossBudget GlobalDominationReduction.SignedEdgeAssembly.missingDiagonalBudget
  exact Finset.sum_le_sum (fun e _ =>
    by
      unfold edgeProduct
      exact PrimeDominationBabyCarrier.weightedOffDiagonalAbs_le_weightedDiagonalBudget
        (A.coupling e) (v (A.left e)) (v (A.right e)))

end SignedEdgeAssembly

end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/-- Every unit sign twist is bounded below by the negative absolute cross budget. -/
theorem offDiagonalRow_retwist_ge_neg_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (twist : Edge -> ℝ)
    (v : Vertex -> ℝ)
    (htwist : ∀ e : Edge, |twist e| = 1) :
    - absoluteCrossBudget A v <=
      (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist).offDiagonalRow v := by
  calc
    - absoluteCrossBudget A v = ∑ e : Edge, -(2 * |edgeProduct A v e|) := by
      unfold absoluteCrossBudget
      rw [Finset.sum_neg_distrib]
    _ <= ∑ e : Edge, 2 * (twist e * A.coupling e) * v (A.left e) * v (A.right e) := by
      apply Finset.sum_le_sum
      intro e _he
      have hedge : - |edgeProduct A v e| <= twist e * edgeProduct A v e := by
        have hneg : - |twist e * edgeProduct A v e| <= twist e * edgeProduct A v e :=
          neg_abs_le (twist e * edgeProduct A v e)
        simpa [abs_mul, htwist e] using hneg
      have hscaled : -(2 * |edgeProduct A v e|) <=
          2 * (twist e * edgeProduct A v e) := by
        nlinarith
      calc
        -(2 * |edgeProduct A v e|) <= 2 * (twist e * edgeProduct A v e) := hscaled
        _ = 2 * (twist e * A.coupling e) * v (A.left e) * v (A.right e) := by
              unfold edgeProduct
              ring
    _ = (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist).offDiagonalRow v := by
      unfold GlobalDominationReduction.SignedEdgeAssembly.offDiagonalRow
      simp [AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist]

/--
For a fixed vector, positivity under every unit sign twist is equivalent to
`arch` dominating the vector-dependent absolute cross budget.
-/
theorem signUniform_nonnegative_iff_absoluteCrossBudget_le_arch
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ) :
    (∀ twist : Edge -> ℝ,
        (∀ e : Edge, |twist e| = 1) ->
          0 <= (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist).completedByArch arch v)
      ↔ absoluteCrossBudget A v <= arch v := by
  constructor
  · intro hnonneg
    have htwist : ∀ e : Edge, |worstTwist A v e| = 1 :=
      abs_worstTwist A v
    have h := hnonneg (worstTwist A v) htwist
    unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch at h
    rw [offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget A v] at h
    linarith
  · intro hdom twist htwist
    have hoff : - absoluteCrossBudget A v <=
        (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist).offDiagonalRow v :=
      offDiagonalRow_retwist_ge_neg_absoluteCrossBudget A twist v htwist
    unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch
    linarith

/--
If the diagonal is smaller than the absolute cross budget for `v`, an explicit
unit sign twist makes the completed form negative at `v`.
-/
theorem exists_unitTwist_negative_of_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (h : arch v < absoluteCrossBudget A v) :
    ∃ twist : Edge -> ℝ,
      (∀ e : Edge, |twist e| = 1) ∧
        (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist).completedByArch arch v < 0 := by
  refine ⟨worstTwist A v, abs_worstTwist A v, ?_⟩
  unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch
  rw [offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget A v]
  linarith

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
The nonnegative slack between the edgewise missing diagonal budget and the
vector-dependent absolute cross budget.
-/
def edgeMismatchResidual (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) : ℝ :=
  ∑ e : Edge,
    |A.coupling e| * (|v (A.left e)| - |v (A.right e)|) ^ 2

omit [Fintype Edge] in
/-- One edge splits into its absolute cross term plus an amplitude-mismatch square. -/
theorem edge_missingBudget_eq_crossBudget_add_mismatch
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) (e : Edge) :
    PrimeDominationBabyCarrier.weightedDiagonalBudget
        (A.coupling e) (v (A.left e)) (v (A.right e))
      = 2 * |edgeProduct A v e|
        + |A.coupling e| * (|v (A.left e)| - |v (A.right e)|) ^ 2 := by
  unfold PrimeDominationBabyCarrier.weightedDiagonalBudget edgeProduct
  have hleft : |v (A.left e)| ^ 2 = v (A.left e) ^ 2 := by
    rw [sq_abs]
  have hright : |v (A.right e)| ^ 2 = v (A.right e) ^ 2 := by
    rw [sq_abs]
  have hcross : |A.coupling e * v (A.left e) * v (A.right e)|
      = |A.coupling e| * |v (A.left e)| * |v (A.right e)| := by
    rw [show A.coupling e * v (A.left e) * v (A.right e)
        = A.coupling e * (v (A.left e) * v (A.right e)) by ring, abs_mul, abs_mul]
    ring
  rw [hcross]
  rw [← hleft, ← hright]
  ring

/-- The edge-mismatch residual is nonnegative. -/
theorem edgeMismatchResidual_nonnegative
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    0 <= edgeMismatchResidual A v := by
  unfold edgeMismatchResidual
  exact Finset.sum_nonneg (fun e _ =>
    mul_nonneg (abs_nonneg (A.coupling e)) (sq_nonneg _))

/--
The usual missing diagonal budget is exactly the adversarial absolute cross
budget plus the amplitude-mismatch residual.
-/
theorem missingDiagonalBudget_eq_absoluteCrossBudget_add_edgeMismatchResidual
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.missingDiagonalBudget v = absoluteCrossBudget A v + edgeMismatchResidual A v := by
  unfold GlobalDominationReduction.SignedEdgeAssembly.missingDiagonalBudget
  unfold absoluteCrossBudget edgeMismatchResidual
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact edge_missingBudget_eq_crossBudget_add_mismatch A v e

/-- The residual decomposition recovers domination of the absolute cross budget. -/
theorem absoluteCrossBudget_le_missingDiagonalBudget_from_residual
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    absoluteCrossBudget A v <= A.missingDiagonalBudget v := by
  rw [missingDiagonalBudget_eq_absoluteCrossBudget_add_edgeMismatchResidual]
  exact le_add_of_nonneg_right (edgeMismatchResidual_nonnegative A v)

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
An abstract certificate predicate is sign-invariant for a fixed row if it
survives every unit retwist of the couplings.
-/
def SignInvariantCertificate
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge) : Prop :=
  ∀ twist : Edge -> ℝ,
    (∀ e : Edge, |twist e| = 1) ->
      Cert A ->
        Cert (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist)

/--
A certificate predicate is sound at `v` if it proves nonnegativity of the
completed row for every certified assembly.
-/
def CertificateSoundAt
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ) : Prop :=
  ∀ B : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge,
    Cert B -> 0 <= B.completedByArch arch v

/--
Any sign-invariant certificate that is sound for completed-row positivity must
pay the vector-dependent absolute cross budget.
-/
theorem absoluteCrossBudget_le_arch_of_signInvariantCertificate
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hcert : Cert A)
    (hinv : SignInvariantCertificate Cert A)
    (hsound : CertificateSoundAt Cert arch v) :
    absoluteCrossBudget A v <= arch v := by
  have htwist : ∀ e : Edge, |worstTwist A v e| = 1 :=
    abs_worstTwist A v
  have hcertTwisted :
      Cert (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v)) :=
    hinv (worstTwist A v) htwist hcert
  have hnonneg :=
    hsound (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v))
      hcertTwisted
  unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch at hnonneg
  rw [offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget A v] at hnonneg
  linarith

/--
If `arch` is below the absolute cross budget, no certified row can have both
unit-retwist invariance and completed-row soundness at `v`.
-/
theorem not_signInvariantCertificate_and_sound_of_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hcert : Cert A)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ¬ (SignInvariantCertificate Cert A ∧ CertificateSoundAt Cert arch v) := by
  intro hboth
  have hbudget : absoluteCrossBudget A v <= arch v :=
    absoluteCrossBudget_le_arch_of_signInvariantCertificate A Cert arch v hcert hboth.1 hboth.2
  linarith

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
A certificate predicate is absolute-coupling invariant at `A` if it only depends
on the endpoints and absolute coupling magnitudes of `A`.
-/
def AbsCouplingInvariantCertificate
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge) : Prop :=
  ∀ B : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge,
    B.left = A.left ->
      B.right = A.right ->
        (∀ e : Edge, |B.coupling e| = |A.coupling e|) ->
          Cert A -> Cert B

omit [Fintype Edge] in
/-- Absolute-coupling invariant certificates are sign-invariant certificates. -/
theorem signInvariantCertificate_of_absCouplingInvariantCertificate
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (habs : AbsCouplingInvariantCertificate Cert A) :
    SignInvariantCertificate Cert A := by
  intro twist htwist hcert
  apply habs (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist)
  · rfl
  · rfl
  · intro e
    simp [AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist, abs_mul, htwist e]
  · exact hcert

/--
Any absolute-coupling invariant certificate that is sound for positivity must
pay the vector-dependent absolute cross budget.
-/
theorem absoluteCrossBudget_le_arch_of_absCouplingInvariantCertificate
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hcert : Cert A)
    (habs : AbsCouplingInvariantCertificate Cert A)
    (hsound : CertificateSoundAt Cert arch v) :
    absoluteCrossBudget A v <= arch v := by
  exact absoluteCrossBudget_le_arch_of_signInvariantCertificate A Cert arch v hcert
    (signInvariantCertificate_of_absCouplingInvariantCertificate A Cert habs) hsound

/--
If `arch` is below the absolute cross budget, no absolute-coupling invariant
certificate can be sound for completed-row positivity at `v` while certifying
`A`.
-/
theorem not_absCouplingInvariantCertificate_and_sound_of_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hcert : Cert A)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ¬ (AbsCouplingInvariantCertificate Cert A ∧ CertificateSoundAt Cert arch v) := by
  intro hboth
  have hbudget : absoluteCrossBudget A v <= arch v :=
    absoluteCrossBudget_le_arch_of_absCouplingInvariantCertificate A Cert arch v hcert hboth.1 hboth.2
  linarith

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
Below the absolute cross budget, any sound certificate must fail on the explicit
adversarial unit retwist.
-/
theorem not_cert_worstRetwist_of_sound_and_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hsound : CertificateSoundAt Cert arch v)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ¬ Cert (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v)) := by
  intro hcertTwisted
  have hnonneg :=
    hsound (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v))
      hcertTwisted
  unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch at hnonneg
  rw [offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget A v] at hnonneg
  linarith

/--
Below the absolute cross budget, every sound certificate has an explicit unit
retwist fake on which it fails.
-/
theorem exists_unitRetwist_not_cert_of_sound_and_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hsound : CertificateSoundAt Cert arch v)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ∃ twist : Edge -> ℝ,
      (∀ e : Edge, |twist e| = 1) ∧
        ¬ Cert (AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A twist) := by
  exact ⟨worstTwist A v, abs_worstTwist A v,
    not_cert_worstRetwist_of_sound_and_arch_lt_absoluteCrossBudget A Cert arch v hsound hsmall⟩

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
The mismatch residual vanishes exactly when every edge either has zero coupling
or equal endpoint magnitudes at `v`.
-/
theorem edgeMismatchResidual_eq_zero_iff
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    edgeMismatchResidual A v = 0 ↔
      ∀ e : Edge, A.coupling e = 0 ∨ |v (A.left e)| = |v (A.right e)| := by
  unfold edgeMismatchResidual
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h e
      have he := h e (Finset.mem_univ e)
      rcases (mul_eq_zero.mp he) with hc | hs
      · left
        exact abs_eq_zero.mp hc
      · right
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro h e _he
      rcases h e with hc | hmag
      · rw [hc, abs_zero, zero_mul]
      · have hsq : (|v (A.left e)| - |v (A.right e)|) ^ 2 = 0 := by
          exact sq_eq_zero_iff.mpr (sub_eq_zero.mpr hmag)
        rw [hsq, mul_zero]
  · intro e _he
    exact mul_nonneg (abs_nonneg (A.coupling e)) (sq_nonneg _)

/--
The standard missing diagonal budget equals the adversarial absolute cross
budget exactly on the no-mismatch locus.
-/
theorem missingDiagonalBudget_eq_absoluteCrossBudget_iff
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ) :
    A.missingDiagonalBudget v = absoluteCrossBudget A v ↔
      ∀ e : Edge, A.coupling e = 0 ∨ |v (A.left e)| = |v (A.right e)| := by
  rw [missingDiagonalBudget_eq_absoluteCrossBudget_add_edgeMismatchResidual]
  constructor
  · intro h
    have hres : edgeMismatchResidual A v = 0 := by
      have hnonneg := edgeMismatchResidual_nonnegative A v
      linarith
    exact (edgeMismatchResidual_eq_zero_iff A v).mp hres
  · intro h
    have hres : edgeMismatchResidual A v = 0 :=
      (edgeMismatchResidual_eq_zero_iff A v).mpr h
    rw [hres]
    ring

/--
If some nonzero-coupling edge has unequal endpoint magnitudes, the standard
missing diagonal budget is strictly larger than the adversarial absolute cross
budget.
-/
theorem absoluteCrossBudget_lt_missingDiagonalBudget_of_exists_active_mismatch
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (v : Vertex -> ℝ)
    (h : ∃ e : Edge,
      A.coupling e ≠ 0 ∧ |v (A.left e)| ≠ |v (A.right e)|) :
    absoluteCrossBudget A v < A.missingDiagonalBudget v := by
  have hle := absoluteCrossBudget_le_missingDiagonalBudget_from_residual A v
  have hne : absoluteCrossBudget A v ≠ A.missingDiagonalBudget v := by
    intro heq
    have hcond : ∀ e : Edge,
        A.coupling e = 0 ∨ |v (A.left e)| = |v (A.right e)| := by
      exact (missingDiagonalBudget_eq_absoluteCrossBudget_iff A v).mp heq.symm
    rcases h with ⟨e, hc, hmag⟩
    rcases hcond e with hc0 | hmag0
    · exact hc hc0
    · exact hmag hmag0
  exact lt_of_le_of_ne hle hne

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder

namespace JensenLadder
namespace AdversarialSignTwistNoGo
namespace SignedEdgeAssembly

variable {Vertex Edge : Type*} [Fintype Edge]

/--
Below the absolute cross budget, there is a same-endpoint, same-absolute-coupling
fake row whose completed form is negative at `v`.
-/
theorem exists_sameAbsRow_negative_of_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ∃ B : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge,
      B.left = A.left ∧
        B.right = A.right ∧
          (∀ e : Edge, |B.coupling e| = |A.coupling e|) ∧
            B.completedByArch arch v < 0 := by
  refine ⟨AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v), ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro e
    simp [AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist, abs_mul, abs_worstTwist A v e]
  · unfold GlobalDominationReduction.SignedEdgeAssembly.completedByArch
    rw [offDiagonalRow_retwist_worstTwist_eq_neg_absoluteCrossBudget A v]
    linarith

/--
If a sound certificate certifies `A` below the absolute cross budget, then a
same-endpoint, same-absolute-coupling fake row is not certified.
-/
theorem exists_sameAbsRow_not_cert_of_cert_sound_and_arch_lt_absoluteCrossBudget
    (A : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge)
    (Cert : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge -> Prop)
    (arch : (Vertex -> ℝ) -> ℝ)
    (v : Vertex -> ℝ)
    (hcert : Cert A)
    (hsound : CertificateSoundAt Cert arch v)
    (hsmall : arch v < absoluteCrossBudget A v) :
    ∃ B : GlobalDominationReduction.SignedEdgeAssembly Vertex Edge,
      B.left = A.left ∧
        B.right = A.right ∧
          (∀ e : Edge, |B.coupling e| = |A.coupling e|) ∧
            Cert A ∧ ¬ Cert B := by
  refine ⟨AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist A (worstTwist A v), ?_, ?_, ?_, hcert, ?_⟩
  · rfl
  · rfl
  · intro e
    simp [AbsoluteBudgetFakeFamilyBlindness.SignedEdgeAssembly.retwist, abs_mul, abs_worstTwist A v e]
  · exact not_cert_worstRetwist_of_sound_and_arch_lt_absoluteCrossBudget A Cert arch v hsound hsmall

end SignedEdgeAssembly
end AdversarialSignTwistNoGo
end JensenLadder
