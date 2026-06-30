import GaloisForLFunctions.CarrierPickKernel

/-!
# The field's central conjectures as Lean statements (the statement-level formalization)

Toward the endpoint "full formal proof in Lean 4": this file makes the field's central
**conjectures first-class Lean `Prop`s** (you formalize the statements before proving them), cleanly
separating what is **proven** (the finite carrier RH-shadow, an actual `theorem`) from what is
**conjectured** (DSS, the infinite-carrier RH-shadow — `def … : Prop`, never asserted). No conjecture
is stated as a proved `theorem`, and no placeholder proof or conjecture axiom is used: a conjecture is
a *definition of a proposition*, which is honest.

* `CarrierHerglotz t` — the FE conjugate-pair carrier is Nevanlinna on `ℂ⁺`;
* `OnLine t` — the zero pair is on the critical line (`Im t = 0`);
* `carrierHerglotz_iff_onLine` — **PROVEN** (`= conj_pair_herglotz_iff`): the finite RH-shadow;
* `DSS` — the difference-Siegel–Shidlovsky conjecture (secular moments algebraically independent),
  a `Prop` (the field's capstone, open).
-/

open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions

noncomputable section

/-- The FE conjugate-pair carrier `m(z) = (t-z)⁻¹ + (conj t - z)⁻¹` is Nevanlinna/Herglotz on `ℂ⁺`. -/
def CarrierHerglotz (t : ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 ≤ ((t - z)⁻¹ + (star t - z)⁻¹).im

/-- The conjugate zero-pair `{t, conj t}` lies on the critical line (`Im t = 0`). -/
def OnLine (t : ℂ) : Prop := t.im = 0

/-- **PROVEN — the finite RH-shadow.** The conjugate-pair carrier is Herglotz on `ℂ⁺` iff the zero
pair is on the critical line. This is the field's RH characterization for one off-line quartet, an
actual theorem (`conj_pair_herglotz_iff`); `RH` is its statement for the infinite carrier `m_ξ`. -/
theorem carrierHerglotz_iff_onLine (t : ℂ) : CarrierHerglotz t ↔ OnLine t :=
  conj_pair_herglotz_iff t

/-- **CONJECTURE (DSS, the field's capstone).** The Difference–Siegel–Shidlovsky conjecture: the
secular moments `P : ℕ → ℂ` (`P_k = Σ_ρ ρ^{-k}`) are algebraically independent over `ℚ` — the
spectrum is arithmetically generic. Equivalent (drafts §8–11) to joint algebraic independence of
`{π} ∪ {ζ(odd)} ∪ {Stieltjes γₙ}`. Stated as a `Prop`; **not** asserted. -/
def DSS (P : ℕ → ℂ) : Prop := AlgebraicIndependent ℚ P

/-- **CONJECTURE (the realization problem #7).** There is a source-built `g` whose self-correlation is
the prime-comb-corrected archimedean kernel — the converse of the field's First Theorem (`B26`).
Stated abstractly as the existence of a Herglotz carrier matching given spectral data `S`. -/
def RealizationProblem (S : ℂ → ℂ) : Prop :=
  ∃ t : ℂ, OnLine t ∧ (fun z => (t - z)⁻¹ + (star t - z)⁻¹) = S

end

end GaloisForLFunctions
