import JensenLadder.C2PResponseNorm
import JensenLadder.C2PLowerRow
import JensenLadder.C2PSuzukiMass

/-!
# Full C2P comparison-certificate consumer

This file composes the C2 response-norm split adapter and the C5 independent
lower-row adapter into the final contradiction consumed by `PacketForce`.

It is deliberately algebraic.  It does not prove the packet response, response
norm, trace comparison, Suzuki component bounds, fake-family failure, or strict
margin.  It only fixes the final Lean handoff shape once those rows exist.

## Honest scope

This is not an RH proof.  It proves only that the named rows are mutually
inconsistent when the margin is strict.  Theorem M is proven, but Theorem M does
not prove RH by itself.
-/

namespace JensenLadder
namespace C2PFullCertificate

/-- Full C2P exclusion from a split C2 comparison certificate and a generic
lower endpoint `LB` for the same observable `cmp`. -/
theorem excluded_of_split_lowerBound
    {cmp proxy NB MB Etrace Emom Ereg Esuzuki Eround Eprime LB : ℝ}
    (hbad : NB ≤ -MB)
    (htrace : |cmp - proxy| ≤ Etrace)
    (hmom : |proxy - NB| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hLB : LB ≤ cmp)
    (hfloorLB : -Eprime ≤ LB)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hcmp :
      |cmp - NB| ≤ Etrace + Emom + Ereg + Esuzuki + Eround := by
    have hbase : |cmp - NB| ≤ Etrace + Emom :=
      C2PResponseNorm.split_bound htrace hmom
    linarith [hEreg_nonneg, hEsuzuki_nonneg, hEround_nonneg]
  have hfloor : -Eprime ≤ cmp :=
    le_trans hfloorLB hLB
  exact PacketForce.excluded_of_comparison hbad hcmp hfloor hmargin

/-- Full C2P exclusion when the packet row is supplied in positive-response
form `MB <= L`, so that `NB := -L`. -/
theorem excluded_of_positiveResponse_split_lowerBound
    {cmp proxy L MB Etrace Emom Ereg Esuzuki Eround Eprime LB : ℝ}
    (hpacket : MB ≤ L)
    (htrace : |cmp - proxy| ≤ Etrace)
    (hmom : |proxy + L| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hLB : LB ≤ cmp)
    (hfloorLB : -Eprime ≤ LB)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hbad : -L ≤ -MB :=
    C2PComparison.negativeBudget_of_positiveResponse hpacket
  have hmom' : |proxy - (-L)| ≤ Emom := by
    simpa [sub_neg_eq_add] using hmom
  exact excluded_of_split_lowerBound hbad htrace hmom'
    hEreg_nonneg hEsuzuki_nonneg hEround_nonneg hLB hfloorLB hmargin

/-- Full C2P exclusion from a split C2 comparison certificate and a Suzuki
component lower-row certificate for the same observable `Q`. -/
theorem excluded_of_split_suzukiLower
    {Q proxy NB MB Etrace Emom Ereg Esuzuki Eround Eprime : ℝ}
    {A L M P R Llo Mhi Phi Rhi : ℝ}
    (hbad : NB ≤ -MB)
    (htrace : |Q - proxy| ≤ Etrace)
    (hmom : |proxy - NB| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hQ : Q = L - A * M - P - R)
    (hA_nonneg : 0 ≤ A)
    (hL : Llo ≤ L)
    (hM : M ≤ Mhi)
    (hP : P ≤ Phi)
    (hR : R ≤ Rhi)
    (hfloor :
      -Eprime ≤ Llo - A * Mhi - Phi - Rhi)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hfloorQ : -Eprime ≤ Q := by
    exact (C2PLowerRow.SuzukiComponentBounds.floor
      { Q := Q
        Eprime := Eprime
        A := A
        L := L
        M := M
        P := P
        R := R
        Llo := Llo
        Mhi := Mhi
        Phi := Phi
        Rhi := Rhi
        hQ := hQ
        hA_nonneg := hA_nonneg
        hL := hL
        hM := hM
        hP := hP
        hR := hR
        hfloor := hfloor })
  have hcmp : |Q - NB| ≤ Etrace + Emom + Ereg + Esuzuki + Eround := by
    have hbase : |Q - NB| ≤ Etrace + Emom :=
      C2PResponseNorm.split_bound htrace hmom
    linarith [hEreg_nonneg, hEsuzuki_nonneg, hEround_nonneg]
  exact PacketForce.excluded_of_comparison hbad hcmp hfloorQ hmargin

/-- Positive-response version of `excluded_of_split_suzukiLower`. -/
theorem excluded_of_positiveResponse_split_suzukiLower
    {Q proxy Lresp MB Etrace Emom Ereg Esuzuki Eround Eprime : ℝ}
    {A L M P R Llo Mhi Phi Rhi : ℝ}
    (hpacket : MB ≤ Lresp)
    (htrace : |Q - proxy| ≤ Etrace)
    (hmom : |proxy + Lresp| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hQ : Q = L - A * M - P - R)
    (hA_nonneg : 0 ≤ A)
    (hL : Llo ≤ L)
    (hM : M ≤ Mhi)
    (hP : P ≤ Phi)
    (hR : R ≤ Rhi)
    (hfloor :
      -Eprime ≤ Llo - A * Mhi - Phi - Rhi)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hbad : -Lresp ≤ -MB :=
    C2PComparison.negativeBudget_of_positiveResponse hpacket
  have hmom' : |proxy - (-Lresp)| ≤ Emom := by
    simpa [sub_neg_eq_add] using hmom
  exact excluded_of_split_suzukiLower hbad htrace hmom'
    hEreg_nonneg hEsuzuki_nonneg hEround_nonneg hQ hA_nonneg
    hL hM hP hR hfloor hmargin

/-- Full C2P exclusion for the fixed C01 ScrewHat observable, using the exact
Lean mass ledger `M_h = 112/15` rather than requiring the certificate to carry a
separate mass upper-bound row. -/
theorem excluded_of_split_fixedOnesSuzukiLower
    {Q proxy NB MB Etrace Emom Ereg Esuzuki Eround Eprime : ℝ}
    {A L P R Llo Phi Rhi : ℝ}
    (hbad : NB ≤ -MB)
    (htrace : |Q - proxy| ≤ Etrace)
    (hmom : |proxy - NB| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hQ : Q = L - A * C2PSuzukiMass.fixedOnesMass - P - R)
    (hA_nonneg : 0 ≤ A)
    (hL : Llo ≤ L)
    (hP : P ≤ Phi)
    (hR : R ≤ Rhi)
    (hfloor :
      -Eprime ≤ Llo - A * ((112 : ℝ) / 15) - Phi - Rhi)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hM : C2PSuzukiMass.fixedOnesMass ≤ (112 : ℝ) / 15 := by
    rw [C2PSuzukiMass.fixedOnesMass_eq]
  exact excluded_of_split_suzukiLower
    (Q := Q) (proxy := proxy) (NB := NB) (MB := MB)
    (Etrace := Etrace) (Emom := Emom) (Ereg := Ereg)
    (Esuzuki := Esuzuki) (Eround := Eround) (Eprime := Eprime)
    (A := A) (L := L) (M := C2PSuzukiMass.fixedOnesMass)
    (P := P) (R := R) (Llo := Llo) (Mhi := (112 : ℝ) / 15)
    (Phi := Phi) (Rhi := Rhi)
    hbad htrace hmom hEreg_nonneg hEsuzuki_nonneg hEround_nonneg
    hQ hA_nonneg hL hM hP hR hfloor hmargin

/-- Positive-response version of
`excluded_of_split_fixedOnesSuzukiLower`. -/
theorem excluded_of_positiveResponse_split_fixedOnesSuzukiLower
    {Q proxy Lresp MB Etrace Emom Ereg Esuzuki Eround Eprime : ℝ}
    {A L P R Llo Phi Rhi : ℝ}
    (hpacket : MB ≤ Lresp)
    (htrace : |Q - proxy| ≤ Etrace)
    (hmom : |proxy + Lresp| ≤ Emom)
    (hEreg_nonneg : 0 ≤ Ereg)
    (hEsuzuki_nonneg : 0 ≤ Esuzuki)
    (hEround_nonneg : 0 ≤ Eround)
    (hQ : Q = L - A * C2PSuzukiMass.fixedOnesMass - P - R)
    (hA_nonneg : 0 ≤ A)
    (hL : Llo ≤ L)
    (hP : P ≤ Phi)
    (hR : R ≤ Rhi)
    (hfloor :
      -Eprime ≤ Llo - A * ((112 : ℝ) / 15) - Phi - Rhi)
    (hmargin : Etrace + Emom + Ereg + Esuzuki + Eround + Eprime < MB) :
    False := by
  have hbad : -Lresp ≤ -MB :=
    C2PComparison.negativeBudget_of_positiveResponse hpacket
  have hmom' : |proxy - (-Lresp)| ≤ Emom := by
    simpa [sub_neg_eq_add] using hmom
  exact excluded_of_split_fixedOnesSuzukiLower
    (Q := Q) (proxy := proxy) (NB := -Lresp) (MB := MB)
    (Etrace := Etrace) (Emom := Emom) (Ereg := Ereg)
    (Esuzuki := Esuzuki) (Eround := Eround) (Eprime := Eprime)
    (A := A) (L := L) (P := P) (R := R) (Llo := Llo)
    (Phi := Phi) (Rhi := Rhi)
    hbad htrace hmom' hEreg_nonneg hEsuzuki_nonneg hEround_nonneg
    hQ hA_nonneg hL hP hR hfloor hmargin

end C2PFullCertificate
end JensenLadder
