import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import JensenLadder.PacketForce

/-!
# C2P affine Newton moment-to-trace bridge

This file formalizes the deterministic algebraic assembly step from
`docs/rh/c2p_moment_trace_bridge_theorem.md`.

The analytic rows remain hypotheses:

* `|A - NB| <= Eaff`: the affine Newton approximation error for the exact
  packet response.
* `|EF j - S j| <= EEF j`: the explicit-formula realization error for each
  additive zero-power coordinate.

The theorem below proves that these rows imply the comparison bound needed by
`JensenLadder.PacketForce.excluded_of_comparison`.

## Honest scope

This is not an RH proof.  It proves only the ordered-field assembly inequality.
The explicit-formula rows, the certified box, the lower row, and the margin are
still open analytic/certificate obligations.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

namespace JensenLadder
namespace MomentTraceBridge

open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι]

/-- The affine trace obtained by replacing additive coordinates by
explicit-formula rows.  In the C2P bridge, `S` is the true additive coordinate
vector and `EF` is the vector supplied by regularized explicit-formula rows. -/
def affineTrace (c : ℝ) (g EF s0 : ι → ℝ) : ℝ :=
  c + ∑ j : ι, g j * (EF j - s0 j)

/-- Difference of two affine traces with the same center and gradient. -/
lemma affineTrace_sub_affineTrace
    (c : ℝ) (g EF S s0 : ι → ℝ) :
    affineTrace c g EF s0 - affineTrace c g S s0 =
      ∑ j : ι, g j * (EF j - S j) := by
  simp [affineTrace]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Per-coordinate explicit-formula errors bound the affine trace error. -/
lemma affineTrace_error_bound
    (c : ℝ) (g EF S s0 EEF : ι → ℝ)
    (hEF : ∀ j, |EF j - S j| ≤ EEF j) :
    |affineTrace c g EF s0 - affineTrace c g S s0| ≤
      ∑ j : ι, |g j| * EEF j := by
  rw [affineTrace_sub_affineTrace]
  calc
    |∑ j : ι, g j * (EF j - S j)|
        ≤ ∑ j : ι, |g j * (EF j - S j)| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (fun j : ι => g j * (EF j - S j)) Finset.univ
    _ = ∑ j : ι, |g j| * |EF j - S j| := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [abs_mul]
    _ ≤ ∑ j : ι, |g j| * EEF j := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_left (hEF j) (abs_nonneg (g j))

/-- **Affine Newton trace comparison, algebraic assembly form.**

`NB` is the exact moment-side packet value, `A` is the affine Newton
approximation evaluated at the true additive zero-power coordinates, and `Q` is
the same affine expression after replacing those coordinates by
explicit-formula rows.

If the packet-to-affine error is at most `Eaff`, and each explicit-formula row
has error `EEF j`, then the total C2P comparison error is bounded by
`Eaff + sum_j |g j| * EEF j`. -/
theorem affineNewtonTraceComparison
    (NB Q A Eaff : ℝ)
    (c : ℝ) (g EF S s0 EEF : ι → ℝ)
    (hA : A = affineTrace c g S s0)
    (hQ : Q = affineTrace c g EF s0)
    (hPacket : |A - NB| ≤ Eaff)
    (hEF : ∀ j, |EF j - S j| ≤ EEF j) :
    |Q - NB| ≤ Eaff + ∑ j : ι, |g j| * EEF j := by
  have hQA : |Q - A| ≤ ∑ j : ι, |g j| * EEF j := by
    rw [hQ, hA]
    exact affineTrace_error_bound c g EF S s0 EEF hEF
  rw [abs_le] at hQA hPacket ⊢
  constructor <;> linarith

/-- If a regularized zero-side trace `Reg` approximates the target coordinate
`S`, and an explicit-formula finite row `EF` approximates `Reg`, then `EF`
approximates `S` with the sum of the two errors. -/
theorem coordinate_error_of_regularized_explicit_formula
    {S Reg EF Ereg Erow : ℝ}
    (hreg : |Reg - S| ≤ Ereg)
    (hrow : |EF - Reg| ≤ Erow) :
    |EF - S| ≤ Ereg + Erow := by
  rw [abs_le] at hreg hrow ⊢
  constructor <;> linarith

/-- Affine Newton comparison when every coordinate is supplied through a
regularized explicit-formula row.

`Reg j` is the exact zero-side value of a regularized/admissible Weil test,
`EF j` is its finite explicit-formula evaluation, `Ereg j` is the
regularization error from the target coordinate `S j` to `Reg j`, and `Erow j`
is the explicit-formula/truncation error from `Reg j` to `EF j`. -/
theorem affineNewtonTraceComparison_of_regularizedRows
    (NB Q A Eaff : ℝ)
    (c : ℝ) (g EF S Reg s0 Ereg Erow : ι → ℝ)
    (hA : A = affineTrace c g S s0)
    (hQ : Q = affineTrace c g EF s0)
    (hPacket : |A - NB| ≤ Eaff)
    (hreg : ∀ j, |Reg j - S j| ≤ Ereg j)
    (hrow : ∀ j, |EF j - Reg j| ≤ Erow j) :
    |Q - NB| ≤ Eaff + ∑ j : ι, |g j| * (Ereg j + Erow j) := by
  exact affineNewtonTraceComparison NB Q A Eaff c g EF S s0
    (fun j => Ereg j + Erow j) hA hQ hPacket
    (fun j => coordinate_error_of_regularized_explicit_formula (hreg j) (hrow j))

/-- **C2P exclusion from the affine Newton bridge.**

This composes `affineNewtonTraceComparison` with
`PacketForce.excluded_of_comparison`.  The analytic obligations remain explicit:
bad packet response, affine Newton error, coordinate-wise explicit-formula
errors, independent lower row, and strict margin. -/
theorem excluded_of_affineNewtonComparison
    (NB Q A MB Eaff Eprime : ℝ)
    (c : ℝ) (g EF S s0 EEF : ι → ℝ)
    (hbad : NB ≤ -MB)
    (hA : A = affineTrace c g S s0)
    (hQ : Q = affineTrace c g EF s0)
    (hPacket : |A - NB| ≤ Eaff)
    (hEF : ∀ j, |EF j - S j| ≤ EEF j)
    (hfloor : -Eprime ≤ Q)
    (hmargin : Eaff + (∑ j : ι, |g j| * EEF j) + Eprime < MB) :
    False := by
  exact PacketForce.excluded_of_comparison
    hbad
    (affineNewtonTraceComparison NB Q A Eaff c g EF S s0 EEF hA hQ hPacket hEF)
    hfloor
    hmargin

/-- **C2P exclusion from regularized explicit-formula coordinate rows.**

This is the theorem interface for the resolvent/Weil-test version of the
moment-to-trace bridge: analytic work supplies the packet-to-affine error, the
coordinate regularization errors, the explicit-formula row errors, and the
lower row.  The deterministic contradiction is then formal. -/
theorem excluded_of_regularizedRows
    (NB Q A MB Eaff Eprime : ℝ)
    (c : ℝ) (g EF S Reg s0 Ereg Erow : ι → ℝ)
    (hbad : NB ≤ -MB)
    (hA : A = affineTrace c g S s0)
    (hQ : Q = affineTrace c g EF s0)
    (hPacket : |A - NB| ≤ Eaff)
    (hreg : ∀ j, |Reg j - S j| ≤ Ereg j)
    (hrow : ∀ j, |EF j - Reg j| ≤ Erow j)
    (hfloor : -Eprime ≤ Q)
    (hmargin : Eaff + (∑ j : ι, |g j| * (Ereg j + Erow j)) + Eprime < MB) :
    False := by
  exact PacketForce.excluded_of_comparison
    hbad
    (affineNewtonTraceComparison_of_regularizedRows
      NB Q A Eaff c g EF S Reg s0 Ereg Erow hA hQ hPacket hreg hrow)
    hfloor
    hmargin

end
end MomentTraceBridge
end JensenLadder
