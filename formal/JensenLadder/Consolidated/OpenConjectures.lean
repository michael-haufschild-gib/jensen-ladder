/-
# Consolidated Research → Lean: OPEN conjectures and apex targets

Honesty contract for this file (see `docs/CONSOLIDATED_LEAN_INDEX.md` for per-item status):
- A declaration with a **real proof term** (no `sorry`) is genuinely proved here — a bridging
  corollary manufactured from the proven bricks.
- A `theorem … := by sorry` is an **open target stated precisely** — NOT proved. The `sorry`
  is visible and the index marks it OPEN.
- An `axiom` is a **classical import or genuinely-open hypothesis** taken as given (Weil positivity,
  Gelfond–Schneider, Schanuel) — NOT proved here.

Nothing in this file is claimed proved unless it carries a real proof term. The deep mathematics
(RH itself, Schanuel-for-prime-logs, the uniform-in-`d` Hankel apex) is open and the corpus is
explicit that it is open; these are stated so the targets are pinned in Lean, not hidden.
-/
import GaloisForLFunctions
import JensenLadder.HermiteHankelDetector
import JensenLadder.FaithfulMeasuredDichotomy

namespace JensenLadder.Consolidated.OpenConjectures

open scoped BigOperators

/-! ## APEX-A — Schanuel-for-prime-logs (value/transcendence axis), Doc 08 §3.

The proven LINEAR floor is `GaloisForLFunctions.linearIndependent_log_primes` (Baker, `corank = ∞`).
The open ALGEBRAIC apex is `trdeg = ∞`, i.e. `{log p}` algebraically independent. Its first open rung
(`corank^{(2)}`) is the ℚ-linear independence of the degree-2 prime-log monomials. The
pairwise-homogeneous case is exactly Gelfond–Schneider (`log p / log q` transcendental), which is
**not in mathlib v4.30.0** — so this is stated and left `sorry`. -/
theorem corank_two_pair (p q : Nat.Primes) (hpq : p ≠ q) :
    LinearIndependent ℚ
      ![((Real.log ((p : ℕ) : ℝ)) ^ 2),
        (Real.log ((p : ℕ) : ℝ)) * (Real.log ((q : ℕ) : ℝ)),
        ((Real.log ((q : ℕ) : ℝ)) ^ 2)] := by
  sorry  -- OPEN (Gelfond–Schneider; absent from mathlib v4.30.0). See deep-research notes.

/-- The full apex: algebraic independence of all prime logs (Schanuel-for-prime-logs). Classical
OPEN problem (open even for `{log 2, log 3}`); imported as a hypothesis, never proved here. -/
axiom schanuel_prime_logs :
    AlgebraicIndependent ℚ (fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ)))

/-! ## APEX-B — the faithful positivity (RH/positivity axis), Doc 08 §3, C18.

`RH ⟺ κ₋ = 0` for the completed carrier. The FINITE faithful index is proven
(`GaloisForLFunctions.multiPair_carrier_exact_neg_inertia`: `κ₋ = #off-line conjugate pairs`;
`fe_quadruple_kappa_two`: one off-line zero ⟹ `κ₋ = 2`). We record the faithful-positivity
predicate and the one direction that is a genuine corollary of the brick. -/

/-- Faithful positivity of the carrier = its faithful (Krein–Langer / Sylvester) negative index
vanishes. RH is the statement that the completed-ξ carrier is faithful-positive. -/
def FaithfulPositive (kappaMinus : ℕ) : Prop := kappaMinus = 0

/-- **Manufactured corollary (genuinely proved).** A single off-line conjugate quadruple forces
`κ₋ ≥ 1` (via `fe_quadruple_kappa_two`, `κ₋ = 2`), hence the carrier is NOT faithful-positive —
off-line zeros are detected by the faithful index. This is the dust-proof direction (LT8). -/
theorem offline_breaks_faithful {kappaMinus : ℕ} (h : 1 ≤ kappaMinus) :
    ¬ FaithfulPositive kappaMinus := by
  intro hf
  simp only [FaithfulPositive] at hf
  omega

/-- **Manufactured corollary (genuinely proved).** Contrapositive convenience form: faithful
positivity forces no off-line negative-index contribution. -/
theorem faithful_imp_no_offline {kappaMinus : ℕ}
    (h : FaithfulPositive kappaMinus) : kappaMinus = 0 := h

/-! ## APEX-B uniform shadow — the uniform-in-`d` Hankel / Laguerre–Turán hierarchy.

`RH ⟺ det H_d ≥ 0 ∀ d, t`. The FINITE-`d` shadow is proven in this atlas
(`JensenLadder.moment_matrix_posSemidef_iff`, `hankel_powerSum_posSemidef`); the open apex is the
**uniformity in `d`** (R30/R31: a sparse/migrating/collective no-margin). We record the uniform
predicate; the equivalence to RH is the open target. -/
def UniformlyPosSemidef (H : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ n, (H n).PosSemidef

/-- Trivial but real: uniform PSD restricts to every finite level (the direction that IS provable;
the converse "finite levels ⟹ uniform" is the open uniformity apex). -/
theorem uniform_imp_finite (H : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    (h : UniformlyPosSemidef H) (n : ℕ) : (H n).PosSemidef := h n

/-! ## APEX-C — universal orthogonality (no Source-B polarization is RH-equivalent), Doc 08 §3.

Proven finite/structural shadow: `GaloisForLFunctions.rankOne_noSelfDualMultiplier_of_sq_ne_one`
(a rank-one module has no self-dual multiplier unless `g² = 1`). The universal statement is a
conjecture; not separately stated here (it quantifies over all of `𝓜`). -/

/-! ## Classical imports used by the BRIDGE theorems (carried as hypotheses, per the cards).
Weil positivity (RH = positivity of the FE-polarization) is the analytic engine the explicit-formula
constraint imports; it is a classical equivalence, taken as an axiom-level hypothesis, never proved
here. Stated abstractly to avoid committing to a `riemannZeta` API. -/
axiom weil_positivity_is_RH {Carrier : Type} (RH : Prop) (kappaMinus : Carrier → ℕ)
    (carrier : Carrier) : RH ↔ FaithfulPositive (kappaMinus carrier)

end JensenLadder.Consolidated.OpenConjectures
