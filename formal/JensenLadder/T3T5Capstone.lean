import Mathlib
import JensenLadder.T3T5Stage0Package
import JensenLadder.SecularReconstruction

/-!
# Stage 5 / T4 of the T3/T5 program: the conditional capstone (boundary HL in the limit ⟹ RH)

This assembles the staged construction into the honest conditional reduction the plan's
Stage 5 specifies (`docs/plans/program_T3_T5_self_product_construction_20260617.md`):

> "This is RH. Honestly: at Stage 5 the program is plausibly RH-equivalent. But it is now a
> statement in a category, with finite referees and a clean firewall, not an estimate against
> a fog."

The plan does **not** claim a proof (§5: "No proof is claimed; this is scaffolding").  The
capstone is therefore the *conditional reduction*: RH follows from the two genuinely-open
inputs surviving Stages 0–4, namely
1. **per-scale positivity** — the Object-X positive quasi-Hermitizing metric `C ≻ 0`
   (Stage 0 Hodge–Riemann ⟺ Weil positivity, `T3T5Stage0`; Stage 4's `J` is its modular
   conjugation), and
2. **convergence** — the secular characteristic polynomials converge locally-uniformly to
   `xiEntire` (Stages 1–3, the faithful construction / rows #2–#3).

The reduction itself is `SecularReconstruction.riemannHypothesis_of_secularCharpoly_quasiHermitian`
(already proved in the atlas: real-rootedness from the metric, entire-ness discharged, Hurwitz
transfer to `xiEntire`).  This module restates it as the **T3/T5 capstone**, making explicit
that the per-scale metric input is exactly the package positivity of Stage 0 and that this is
the entire remaining wall (= T4 = the no-margin sign = RH-equivalent).  Axiom-clean (inherits
the secular reduction's axioms).
-/

namespace JensenLadder
namespace T3T5Capstone

open Matrix
open scoped Matrix ComplexOrder

/-- **T3/T5 capstone (conditional reduction = Stage 5 / T4).**
If a scale-indexed family of secular reconstruction matrices `M n`
(i) admits, at every scale, a positive-definite quasi-Hermitizing metric `η`
(the Object-X `C ≻ 0` = the Stage-0 Weil/Hodge–Riemann positivity, whose modular
conjugation is the Stage-4 `J`), and
(ii) has characteristic polynomials `F n` converging locally uniformly to `HurwitzBridge.xiEntire`
(the Stage 1–3 faithful construction / convergence rows),
then the **Riemann Hypothesis holds**.

This is the honest capstone: it is RH-equivalent (the per-scale positivity in the limit *is*
Weil positivity), stated as a reduction in the category, with the two inputs being exactly the
open parts the plan isolates.  It proves RH *from* those inputs; it does not prove them. -/
theorem riemannHypothesis_of_packagePositivity_and_convergence
    {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (M : ∀ n, Matrix (ι n) (ι n) ℂ)
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n z, F n z = (M n - z • (1 : Matrix (ι n) (ι n) ℂ)).det)
    (hposMetric : ∀ n, ∃ η : Matrix (ι n) (ι n) ℂ, η.PosDef ∧ η * (M n) = (M n)ᴴ * η)
    (hconv : TendstoLocallyUniformlyOn F HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis :=
  SecularReconstruction.riemannHypothesis_of_secularCharpoly_quasiHermitian M F hF hposMetric hconv

end T3T5Capstone
end JensenLadder
