import Mathlib.Tactic

/-!
# The weighted prime-quarantine trace gate

One operator-algebraic lead for RH (object_x.md, AHSMI) seeks a hidden source
algebra with orthogonal prime-label isometries `v_p` in which an off-line zero
appears as a finite positive "defect" projection `Q` of the bulk, quarantined by
the prime insertions.  A **confirmed no-go** bounds this from the trace side.

In a semifinite source core with orthogonal prime-label isometries and a
finite, faithful, normalized trace `τ`, suppose a finite positive defect `Q`
(trace `t = τ(Q) ≥ 0`) is *subharmonic* for the raw weighted prime transfer
`L_σ(Q) = Σ_{p∈P} a_p · v_p Q v_p^*`, i.e. `L_σ(Q) ≤ Q`.  Because each
`v_p (·) v_p^*` is trace-preserving, applying `τ` gives `(Σ_{p∈P} a_p)·t ≤ t`.

If the finite weight sum exceeds `1`, this forces `t = 0`: **no finite positive
defect can be subharmonic for the raw positive transfer when `Σ a_p > 1`.**  For
the strip weights `a_p = p^{-σ}` with `½ < σ < 1`, finite prime sets with
`Σ_{p∈P} p^{-σ} > 1` exist (e.g. `2^{-σ}+3^{-σ}+5^{-σ} > 1` already for
`σ` near `½`), so the raw transfer `L_σ` is **supercritical** in the entire
critical strip.

Consequence (the no-go): a surviving RH-false defect cannot be a bound state of
the *raw positive* transfer `L_σ`.  It must be a bound state of the **signed,
PNT-normalized** transfer `R_σ = L_σ − (pole/PNT equilibrium) − (gamma
counterterm)` — i.e. the positive first-layer KMS correspondence pays the `s=1`
pole and quarantines everything finite; the RH content lives only in the signed
boundary fluctuation, after subtraction.  This matches the atlas's no-margin /
"the inequality is never the crossing" theme.

This module formalizes the trace inequality core.  The semifinite-trace and
isometry structure (`v_p`, `τ(v_p Q v_p^*) = τ(Q)`) is the cited operator-algebra
input; the load-bearing arithmetic is the real inequality below.

The useful residue is a no-go: raw positive prime transfer is supercritical in
the critical strip, so any surviving finite defect must come from the signed,
normalized boundary fluctuation rather than from raw positivity.
-/

namespace JensenLadder
namespace PrimeQuarantineTraceNoGo

/-- **Quarantine trace gate.**  If a finite positive defect has trace `t ≥ 0`,
is subharmonic for the raw weighted prime transfer (`W · t ≤ t`, where
`W = Σ_{p∈P} a_p` is the finite weight sum), and the weight sum exceeds `1`, then
the defect is traceless (`t = 0`).  Hence no finite RH-false projection survives
the raw positive transfer in the supercritical (`W > 1`) regime. -/
theorem quarantine_trace_zero_of_weight_gt_one
    {t W : ℝ} (ht : 0 ≤ t) (hsub : W * t ≤ t) (hW : 1 < W) : t = 0 := by
  by_contra h
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
  nlinarith [mul_pos (by linarith : (0 : ℝ) < W - 1) htpos]

/-- Contrapositive: a finite *positive*-trace defect (`t > 0`) cannot be
subharmonic for a supercritical weighted transfer (`W > 1`).  A surviving
defect must therefore be sourced by the signed/normalized transfer `R_σ`, not
the raw positive `L_σ`. -/
theorem not_subharmonic_of_pos_trace_and_supercritical
    {t W : ℝ} (htpos : 0 < t) (hW : 1 < W) : ¬ (W * t ≤ t) := by
  intro hsub
  exact (ne_of_gt htpos) (quarantine_trace_zero_of_weight_gt_one htpos.le hsub hW)

end PrimeQuarantineTraceNoGo
end JensenLadder
