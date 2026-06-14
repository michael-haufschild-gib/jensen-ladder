import JensenLadder.C2PComparison

/-!
# C2P response-norm split interface

This file packages the ordered-field assembly for the C2 comparison row

```text
  |Q_{H_B}^xi - N_B(Phi_xi)| <= Ecmp.
```

The analytic backend described in
`docs/rh/c2p_cmp_response_norm_backend_report.md` splits the comparison through
a moment-side proxy:

```text
  Q_{H_B}^xi  --Etrace-->  R_H^mom(Phi_xi)  --Emom-->  N_B(Phi_xi).
```

This file proves only the deterministic triangle-inequality assembly.  The
moment-proxy interval norm, coefficient-to-trace comparison, admissibility,
remainder, and rounding estimates remain hypotheses.

## Honest scope

This is not an RH proof.  It only packages the C2 row once the analytic
response-norm certificate exists.  Theorem M is proven, but Theorem M does not
prove RH by itself.
-/

namespace JensenLadder
namespace C2PResponseNorm

/-- Two absolute-error bounds compose through a proxy. -/
theorem split_bound
    {cmp proxy NB Etrace Emom : ℝ}
    (htrace : |cmp - proxy| ≤ Etrace)
    (hmom : |proxy - NB| ≤ Emom) :
    |cmp - NB| ≤ Etrace + Emom := by
  rw [abs_le] at htrace hmom ⊢
  constructor <;> linarith

/-- The response-norm split certificate used for the C2 comparison row. -/
structure SplitRows where
  cmp : ℝ
  proxy : ℝ
  NB : ℝ
  Etrace : ℝ
  Emom : ℝ
  Ereg : ℝ
  Esuzuki : ℝ
  Eround : ℝ
  htrace : |cmp - proxy| ≤ Etrace
  hmom : |proxy - NB| ≤ Emom
  hEreg_nonneg : 0 ≤ Ereg
  hEsuzuki_nonneg : 0 ≤ Esuzuki
  hEround_nonneg : 0 ≤ Eround

/-- The total comparison budget represented by a split response-norm
certificate. -/
def SplitRows.Ecmp (C : SplitRows) : ℝ :=
  C.Etrace + C.Emom + C.Ereg + C.Esuzuki + C.Eround

/-- The split certificate gives the C2 comparison row. -/
theorem SplitRows.comparison_bound (C : SplitRows) :
    |C.cmp - C.NB| ≤ C.Ecmp := by
  have hbase : |C.cmp - C.NB| ≤ C.Etrace + C.Emom :=
    split_bound C.htrace C.hmom
  unfold SplitRows.Ecmp
  linarith [C.hEreg_nonneg, C.hEsuzuki_nonneg, C.hEround_nonneg]

/-- Full C2P comparison rows from a split response-norm certificate, lower row,
bad packet row, and margin. -/
structure SplitComparisonCertificate where
  rows : SplitRows
  MB : ℝ
  Eprime : ℝ
  hbad : rows.NB ≤ -MB
  hfloor : -Eprime ≤ rows.cmp
  hmargin : rows.Ecmp + Eprime < MB

/-- A split response-norm certificate excludes the packet after the independent
lower row and strict margin are supplied. -/
theorem SplitComparisonCertificate.excluded (C : SplitComparisonCertificate) :
    False :=
  PacketForce.excluded_of_comparison
    C.hbad C.rows.comparison_bound C.hfloor C.hmargin

/-- If a packet source is written in positive-response convention `MB <= L`,
the split certificate can be consumed directly with `NB = -L`. -/
theorem excluded_of_positiveResponse_split
    {cmp proxy L MB Etrace Emom Ereg Esuzuki Eround Eprime : ℝ}
    (hpacket : MB ≤ L)
    (htrace : |cmp - proxy| ≤ Etrace)
    (hmom : |proxy + L| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hfloor : -Eprime ≤ cmp)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hmom' : |proxy - (-L)| ≤ Emom := by
    simpa [sub_neg_eq_add] using hmom
  have hcmp : |cmp - (-L)| ≤ Etrace + Emom + Ereg + Esuzuki + Eround := by
    have hbase : |cmp - (-L)| ≤ Etrace + Emom :=
      split_bound htrace hmom'
    linarith
      [hEreg_nonneg, hEsuzuki_nonneg, hEround_nonneg]
  have hcmp_plus : |cmp + L| ≤ Etrace + Emom + Ereg + Esuzuki + Eround := by
    simpa [sub_neg_eq_add] using hcmp
  exact C2PComparison.excluded_of_positiveResponse
    hpacket hcmp_plus hfloor hmargin

end C2PResponseNorm
end JensenLadder
