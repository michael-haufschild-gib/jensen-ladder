import JensenLadder.MomentTraceBridge

/-!
# C2P comparison certificate interface

This file packages the row signatures used by the C2P comparison route.

It does not prove any analytic input.  It only prevents sign-convention and
row-name drift between the packet response, the comparison row, the independent
lower row, and the deterministic contradiction already formalized in
`JensenLadder.PacketForce` and `JensenLadder.MomentTraceBridge`.

## Honest scope

The analytic rows remain hypotheses: bad-packet response, comparison error,
regularized explicit-formula rows, lower row, and strict margin.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace C2PComparison

open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι]

/-- Convert a positive packet response `MB <= L` into the negative-budget
convention `NB <= -MB` with `NB = -L`. -/
theorem negativeBudget_of_positiveResponse {L MB : ℝ}
    (hpacket : MB ≤ L) :
    -L ≤ -MB := by
  linarith

/-- The four real inequalities consumed by the comparison-form PacketForce
contradiction. -/
structure ComparisonRows where
  cmp : ℝ
  NB : ℝ
  MB : ℝ
  Ecmp : ℝ
  Eprime : ℝ
  hbad : NB ≤ -MB
  hcmp : |cmp - NB| ≤ Ecmp
  hfloor : -Eprime ≤ cmp
  hmargin : Ecmp + Eprime < MB

/-- A completed comparison-row certificate excludes the packet. -/
theorem ComparisonRows.excluded (C : ComparisonRows) :
    False :=
  PacketForce.excluded_of_comparison
    C.hbad C.hcmp C.hfloor C.hmargin

/-- Comparison exclusion when the packet source is recorded in positive-response
form `MB <= L`.  The comparison row is then written against `NB = -L`, hence
`|cmp + L| <= Ecmp`. -/
theorem excluded_of_positiveResponse
    {cmp L MB Ecmp Eprime : ℝ}
    (hpacket : MB ≤ L)
    (hcmp : |cmp + L| ≤ Ecmp)
    (hfloor : -Eprime ≤ cmp)
    (hmargin : Ecmp + Eprime < MB) :
    False := by
  have hbad : -L ≤ -MB := negativeBudget_of_positiveResponse hpacket
  have hcmp' : |cmp - (-L)| ≤ Ecmp := by
    simpa [sub_neg_eq_add] using hcmp
  exact PacketForce.excluded_of_comparison hbad hcmp' hfloor hmargin

/-- The regularized-row C2P certificate bundle.

`NB` is the negative-budget packet value, `A` is the affine approximation at the
target additive coordinates `S`, and `Q` is the affine expression after those
coordinates are replaced by regularized explicit-formula rows `EF`.
-/
structure RegularizedRows where
  NB : ℝ
  Q : ℝ
  A : ℝ
  MB : ℝ
  Eaff : ℝ
  Eprime : ℝ
  c : ℝ
  g : ι → ℝ
  EF : ι → ℝ
  S : ι → ℝ
  Reg : ι → ℝ
  s0 : ι → ℝ
  Ereg : ι → ℝ
  Erow : ι → ℝ
  hbad : NB ≤ -MB
  hA : A = MomentTraceBridge.affineTrace c g S s0
  hQ : Q = MomentTraceBridge.affineTrace c g EF s0
  hPacket : |A - NB| ≤ Eaff
  hreg : ∀ j, |Reg j - S j| ≤ Ereg j
  hrow : ∀ j, |EF j - Reg j| ≤ Erow j
  hfloor : -Eprime ≤ Q
  hmargin :
    Eaff + (∑ j : ι, |g j| * (Ereg j + Erow j)) + Eprime < MB

/-- The comparison error represented by a regularized-row certificate. -/
def RegularizedRows.Ecmp (C : RegularizedRows (ι := ι)) : ℝ :=
  C.Eaff + ∑ j : ι, |C.g j| * (C.Ereg j + C.Erow j)

/-- A regularized-row certificate supplies the comparison row required by
`PacketForce.excluded_of_comparison`. -/
theorem RegularizedRows.comparison_bound (C : RegularizedRows (ι := ι)) :
    |C.Q - C.NB| ≤ C.Ecmp := by
  exact MomentTraceBridge.affineNewtonTraceComparison_of_regularizedRows
    C.NB C.Q C.A C.Eaff C.c C.g C.EF C.S C.Reg C.s0 C.Ereg C.Erow
    C.hA C.hQ C.hPacket C.hreg C.hrow

/-- A completed regularized-row certificate excludes the packet. -/
theorem RegularizedRows.excluded (C : RegularizedRows (ι := ι)) :
    False := by
  exact MomentTraceBridge.excluded_of_regularizedRows
    C.NB C.Q C.A C.MB C.Eaff C.Eprime C.c C.g C.EF C.S C.Reg C.s0 C.Ereg C.Erow
    C.hbad C.hA C.hQ C.hPacket C.hreg C.hrow C.hfloor C.hmargin

end
end C2PComparison
end JensenLadder
