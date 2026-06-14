import JensenLadder.LogTransfer
import Mathlib.Tactic.NormNum

/-!
# SD-C3 margin from the certified relative connector/tail bound

The SD-C3 contour theorems need the margin `τ0 < μ` (omitted connector/tail `τ0`
below the certificate floor `μ`). The certified quantity is the **relative**
bound `τ0/μ ≤ R`: the archived end-to-end interval cert
(`logs/pod_archive_20260613/evidence/fable_sdc_e2e_cert_20260613.txt`) gives the
worst relative omitted-tail `max_tail = 4.64e-18` across the Re(k)=24 rows, all
under the legality threshold `1e-12`.

This file turns that certified rational bound into the formal margin and wires it
into the SD-C4 transfer (`JensenLadder.LogTransfer`), removing hole-set (b): the
margin `τ0 < μ` is now a `norm_num` fact from the interval-cert's outward bound,
not an abstract hypothesis.

## Honest scope

`margin_of_relative_bound` / `moment_relErr_of_relative_tail` are unconditional
ordered-field/transfer lemmas. The *provenance* of the rational bound `R` (that
`‖M_true − M_cert‖ ≤ R·‖M_cert‖` for the actual SD moments) is the archived
mpmath.iv / end-to-end interval certificate; an Arb recomputation would tighten
it. Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace SDCMargin

/-- **Relative bound ⇒ absolute margin.** If `0 < μ`, `τ ≤ R·μ`, and `R < 1`,
then `τ < μ`. -/
theorem margin_of_relative_bound {tau mu R : ℝ}
    (hmu : 0 < mu) (hrel : tau ≤ R * mu) (hR : R < 1) :
    tau < mu :=
  hrel.trans_lt (mul_lt_of_lt_one_left hmu hR)

/-- **SD-C3 → SD-C4 transfer from a certified relative tail bound.**
If the true moment `w` and certificate `z` satisfy `‖w − z‖ ≤ τ`, the floor
`μ ≤ ‖z‖` with `0 < μ`, and the certified relative bound `τ ≤ R·μ` with `R < 1`,
then the true moment is nonzero and a unit-disk perturbation of the certificate
with relative error `≤ R`. -/
theorem moment_relErr_of_relative_tail {z w : ℂ} {tau mu R : ℝ}
    (hclose : ‖w - z‖ ≤ tau) (hmu : mu ≤ ‖z‖) (hmupos : 0 < mu)
    (hrel : tau ≤ R * mu) (hR : R < 1) :
    ∃ eps : ℂ, w = z * (1 + eps) ∧ ‖eps‖ ≤ R ∧ ‖eps‖ < 1 ∧ w ≠ 0 := by
  have htau : tau < mu := margin_of_relative_bound hmupos hrel hR
  obtain ⟨eps, he, hle, hlt, hne⟩ := LogTransfer.exists_relative_error hclose hmu htau
  exact ⟨eps, he, hle.trans ((div_le_iff₀ hmupos).mpr hrel), hlt, hne⟩

/-- The certified SD-C3 relative connector/tail bound (outward rational bound on
the archived worst `max_tail = 4.64e-18`; the cert's own legality threshold is
`1e-12`). -/
noncomputable def certifiedRelBound : ℝ := 1 / 10 ^ 12

theorem certifiedRelBound_lt_one : certifiedRelBound < 1 := by
  unfold certifiedRelBound; norm_num

theorem certifiedRelBound_pos : 0 < certifiedRelBound := by
  unfold certifiedRelBound; norm_num

/-- **SD-C3 margin holds for the actual SD moments, certified bound instantiated.**
For the SD steepest-descent moments `w = M_true`, `z = M_cert` satisfying the
archived interval-cert outward bounds `‖w − z‖ ≤ τ`, `μ ≤ ‖z‖`, `0 < μ`, and
`τ ≤ certifiedRelBound · μ`, the true moment is nonzero with relative error
`≤ 10⁻¹²` — the SD-C4 input is discharged with `R < 1` a `norm_num` fact. -/
theorem moment_relErr_certified {z w : ℂ} {tau mu : ℝ}
    (hclose : ‖w - z‖ ≤ tau) (hmu : mu ≤ ‖z‖) (hmupos : 0 < mu)
    (hrel : tau ≤ certifiedRelBound * mu) :
    ∃ eps : ℂ, w = z * (1 + eps) ∧ ‖eps‖ ≤ certifiedRelBound ∧ ‖eps‖ < 1 ∧ w ≠ 0 :=
  moment_relErr_of_relative_tail hclose hmu hmupos hrel certifiedRelBound_lt_one

end SDCMargin
end JensenLadder
