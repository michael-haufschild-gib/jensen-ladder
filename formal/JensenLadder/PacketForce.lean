import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# C2P Row-P2 exclusion core (deterministic assembly)

This file formalizes the deterministic *assembly* step of GPT-2's C2P Row-P2
program (`docs/rh/c2p_row_p2_theorem_ledger.md`, `c2p_arithmetic_transfer_direct_attempt.md`):
the logic that turns the analytic rows into the exclusion of a bad packet.

It is the Row-P2 analogue of the SD-C consumer cores
(`JensenLadder.LogTransfer`, `JensenLadder.ContourLegality`): the hard analytic
inputs — the *multiplicative packet-to-prime forcing* row P2, the comparison
error `E_cmp`, the independent prime/gamma lower row P3 — enter as hypotheses
(they are GPT-2's open theorem debt), and this file proves that once they hold
with the margin P4, the bad packet is excluded.

`Q` denotes the full Suzuki/Weil form value `Q_h^xi(c_B)`; `MB` the packet
margin `M_B`; `cmp` the Weil/Suzuki response value `v_B^T G_xi(F_B) v_B`; `NB`
the packet response `N_B(Φ_xi)`.

## Honest scope

This proves only the assembly inequalities (pure ordered-field arithmetic). It
does **not** prove P2 (the multiplicativity forcing), the existence of a small
enough `E_cmp`, or P3 — those are the load-bearing analytic theorems GPT-2 owns.
Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace PacketForce

/-- **Row-P2 forcing pushes the form below the lower floor.**
The forcing row P2 (`Q ≤ -MB + Eforce`, with `Eforce = E_force+E_tail+E_adm`)
together with the margin P4 (`Eforce + Elower < MB`) drives the full Suzuki/Weil
form strictly below the floor `-Elower` that the independent lower row P3 must
respect. -/
theorem force_below_lower_floor
    {Q MB Eforce Elower : ℝ}
    (hP2 : Q ≤ -MB + Eforce)
    (hP4 : Eforce + Elower < MB) :
    Q < -Elower := by
  linarith

/-- **Row-P2 exclusion (direct forcing form).**
P2 (forcing) + P3 (independent lower row `-Elower ≤ Q`) + P4 (margin) are jointly
contradictory: the bad packet is excluded. -/
theorem excluded_of_force_lower_margin
    {Q MB Eforce Elower : ℝ}
    (hP2 : Q ≤ -MB + Eforce)
    (hP3 : -Elower ≤ Q)
    (hP4 : Eforce + Elower < MB) :
    False := by
  linarith

/-- **Comparison form pushes the response below the floor.**
The surviving `PacketResponseWeilComparison` shape (N048): a bad packet response
`NB ≤ -MB`, the comparison bound `|cmp - NB| ≤ Ecmp` tying the Weil/Suzuki form
value `cmp` to the packet response, and the margin `Ecmp + Eprime < MB` force
`cmp < -Eprime`. -/
theorem comparison_below_floor
    {cmp NB MB Ecmp Eprime : ℝ}
    (hbad : NB ≤ -MB)
    (hcmp : |cmp - NB| ≤ Ecmp)
    (hmargin : Ecmp + Eprime < MB) :
    cmp < -Eprime := by
  rw [abs_le] at hcmp
  linarith [hcmp.1, hcmp.2]

/-- **Row-P2 exclusion (comparison form).**
Bad packet response, comparison bound, the independent prime/gamma floor
`-Eprime ≤ cmp`, and the margin are jointly contradictory: the bad packet is
excluded.  This is the deductive core of `PacketResponseWeilComparison`. -/
theorem excluded_of_comparison
    {cmp NB MB Ecmp Eprime : ℝ}
    (hbad : NB ≤ -MB)
    (hcmp : |cmp - NB| ≤ Ecmp)
    (hfloor : -Eprime ≤ cmp)
    (hmargin : Ecmp + Eprime < MB) :
    False := by
  rw [abs_le] at hcmp
  linarith [hcmp.1, hcmp.2]

end PacketForce
end JensenLadder
