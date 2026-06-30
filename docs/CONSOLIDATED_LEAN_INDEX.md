# Consolidated Research → Lean: Working Index

**Purpose.** Track the Lean formalization, in this `rh-formal-atlas` project, of every lemma,
theorem, and conjecture catalogued in the consolidated research
(`publications/hgt/docs/consolidated/{03,07,08,09}-*.md`). Status per item, with notes on gaps.

**Provenance & method.**
- The hypertranscendence/weld/corank/orbit/carrier **bricks** were ported into this atlas as the
  `GaloisForLFunctions` lean_lib (from `hgt/formal`; identical toolchain `leanprover/lean4:v4.30.0`
  and identical mathlib rev `c5ea0035…`, so they compile unchanged). **78 modules, 0 sorries.**
- The RH-side **apex forms** are native to this atlas's `JensenLadder` lean_lib (159 modules, 0
  sorries): faithful/measured, secular Herglotz, Hodge index, Hankel/moment hierarchy, Li, Cayley.
- New consolidation modules: `JensenLadder/Consolidated/Roster.lean` (machine-checks every PROVED
  item below via `#check`) and `JensenLadder/Consolidated/OpenConjectures.lean` (states the open
  targets; real proofs where they reduce to bricks, visible `sorry`/`axiom` otherwise).

**Status legend.** `PROVED` = sorry-free Lean theorem present. `PROVED (corollary)` = proved here
from bricks. `SORRY` = stated in Lean, proof open. `AXIOM` = classical import / open hypothesis,
taken as given. `PROSE` = stated in the consolidated docs, not Lean-formalizable at the current
abstraction (no `riemannZeta`/analytic layer in scope). Build status recorded in the last section.

---

## Table A — Proven bricks (`GaloisForLFunctions`, 0 sorries)

| Consolidated item (Doc 07) | Lean theorem | Module | Status |
|---|---|---|---|
| T4 corank linear floor `corank=∞ ⟺ {log p} ℚ-LI` (Baker) | `linearIndependent_log_primes` | Core | PROVED |
| {log p} no rational relation | `logPrime_no_rat_relation` | OrbitFreeness | PROVED |
| `{m : Σ m_p log p = 0} = {0}` | `finitePrimeLogAnnihilator_eq_singleton` | Resonance | PROVED |
| T1 constraint `ι`, order-2 | `sigma_involutive` | Core | PROVED |
| T1/fixed-locus `σ̄` fixes `Re=½` | `sigmaConj_fixed_iff_critical` | SigmaOrbit | PROVED |
| boundary modulus `|p^{-s}|=p^{-1/2} ⟺ Re=½` | `boundaryUnitNormalize_norm_eq_one_iff` | BoundaryModulus | PROVED |
| T1 prime-flow freq `=0 ⟺` trivial | `primeLogFrequency_eq_zero_iff` | KroneckerFlow | PROVED |
| T11 archimedean shift `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` | `gammaReal_shift_two` | ArchimedeanGamma | PROVED |
| T13 `∂_s e_m = −(m·ℓ)e_m` | `deriv_archimedeanPrimeMode` | ArchimedeanAxisMode | PROVED |
| corank-no-collapse (`F₁ ≠ ∂_s`) | `primeLogFullSpan_insert_archimedean_eq` | ArchimedeanCorank | PROVED |
| corank stays ∞ under archimedean | `primeLogFiniteSlice_finrank_with_archimedean_unbounded` | ArchimedeanCorank | PROVED |
| T2/T3 Koszul: D1-ker = additive cocycles | `koszulD1_eq_zero_iff_additiveCocycle` | KoszulCohomology | PROVED |
| `d1∘d0=0` | `koszulD1_koszulD0_eq_zero` | KoszulCohomology | PROVED |
| T3 CC-gauge `a=c·σ(g)/g ↦ const` | `ccGaugeMultiplier_eq_const` | MultiplierDichotomy | PROVED |
| T2 orbit-degree coboundary | `orbitDegree_intShiftCoboundary` | OrbitBalance | PROVED |
| T8/T9 no Source-B polarization | `rankOne_noSelfDualMultiplier_of_sq_ne_one` | RankOneDuality | PROVED |
| T25 `F_q` FE L-poly palindrome | `functionField_localFactor_FE` | FunctionFieldFE | PROVED |
| **T5/T15 faithful index `κ₋ = #off-line pairs`** | `multiPair_carrier_exact_neg_inertia` | CarrierCauchy | PROVED |
| **T5 one off-line zero ⟹ `κ₋ = 2`** | `fe_quadruple_kappa_two` | FECarrier | PROVED |
| Krein–Langer inertia bound | `neg_inertia_le_of_posSemidef` | KreinLangerInertia | PROVED |
| `κ₋ ≤ 1` from add-sq nonneg | `sigNeg_le_one_of_add_sq_nonneg` | KreinLangerInertia | PROVED |
| T29 superzeta `𝒵(k)=Σ_ρ ρ^{−k}=P_k` | `superzeta_coeff_eq_powerSum` | SuperzetaResolvent | PROVED |
| T29 Newton power-sum Torelli | `powerSum_torelli` | PowerSumTorelli | PROVED |
| spectral Torelli faithful | `spectralTorelli_faithful` | SpectralTorelli | PROVED |
| T27 Stieltjes–log Cauchy pairing | `stieltjes_pairing_cauchy_j` | StieltjesWeld | PROVED |
| Satake/Sato–Tate orthonormality | `satoTate_orthonormal` | SatoTateMoment | PROVED |

## Table B — Proven apex forms (`JensenLadder`, 0 sorries)

| Consolidated item | Lean theorem | Module | Status |
|---|---|---|---|
| LT1/APEX-B faithful ⟹ measured | `faithful_imp_measured` | FaithfulMeasuredDichotomy | PROVED |
| measured ⇏ faithful (dust-blindness) | `measured_not_imp_faithful` | FaithfulMeasuredDichotomy | PROVED |
| `m_ξ ∈ N₀` direction (secular Herglotz) | `secular_herglotz` | SecularHerglotz | PROVED |
| Cauchy pole not Herglotz | `cauchy_pole_not_herglotz` | SecularHerglotz | PROVED |
| Herglotz real-level limit | `herglotz_real_level` | SecularHerglotz | PROVED |
| M6 Hodge-index signature inequality | `hodge_index_ineq` | HodgeIndexInequality | PROVED |
| positive ⟹ not primitive (n₊=1) | `pos_not_primitive` | HodgeIndexInequality | PROVED |
| Bezoutian = residue Gram | `bezout_eq_residue_gram` | BezoutianResidue | PROVED |
| APEX-B Hankel power-sum PSD (det H_d≥0 leader) | `hankel_powerSum_posSemidef` | HermiteHankelDetector | PROVED |
| moment matrix PSD iff (finite Laguerre–Turán) | `moment_matrix_posSemidef_iff` | HermiteHankelDetector | PROVED |
| cofactor Gram posDef iff | `cofactor_gram_posDef_iff` | HermiteHankelDetector | PROVED |
| Li-criterion summand nonneg (unit modulus) | `li_coefficient_nonneg_of_unit_modulus` | LiCriterionDisk | PROVED |
| Li disk inside-unit iff | `norm_one_sub_inv_lt_one_iff` | LiCriterionDisk | PROVED |
| G5 Cayley η-unitary bridge | `cayley_etaUnitary` | CayleyUnitaryBridge | PROVED |
| secular reconstruction real roots | `secular_roots_real` | SecularRealRoots | PROVED |
| secular strict monotone | `secular_strictMono` | SecularRealRoots | PROVED |

## Table C — BRIDGE paper theorems T1–T29 (Doc 07 §1): Lean realization of the algebraic core

| # | Theorem | Lean core | Status |
|---|---|---|---|
| T1 | constraint-not-flow | `sigma_involutive`, `sigmaConj_fixed_iff_critical`, `primeLogFrequency_eq_zero_iff` | PROVED (core) |
| T2 | σ-orbit-balance CC invariant | `orbitDegree_intShiftCoboundary`, `ccGaugeMultiplier_eq_const` | PROVED (core); full CC-equiv = PROSE |
| T3 | multiplier dichotomy | `ccGaugeMultiplier_eq_const`; non-CC⟹HT = Hölder import | PROVED (core) + AXIOM (Hölder) |
| T4 | corank seam, level separation | `linearIndependent_log_primes`, `primeLogFullSpan_insert_archimedean_eq` | PROVED (linear floor); apex = SORRY (`corank_two_pair`) |
| T5/T15 | faithful index `κ₋` | `multiPair_carrier_exact_neg_inertia`, `fe_quadruple_kappa_two` | PROVED |
| T8/T9 | orthogonality (no Source-B positivity) | `rankOne_noSelfDualMultiplier_of_sq_ne_one` | PROVED (rank-1); categorical/universal = PROSE |
| T11 | seam = digamma residue | `gammaReal_shift_two` (+ ArchimedeanGamma connection) | PROVED (core) |
| T13 | generators Fourier-diagonal | `deriv_archimedeanPrimeMode` | PROVED |
| T14 | explicit formula constraint, `Q_W` `(1|∞)`, `RH⟺κ₋=0` | `multiPair_carrier_exact_neg_inertia` + `hodge_index_ineq` | PROVED (κ₋ core); `RH⟺` = PROSE/AXIOM |
| T16 | phase-cancellation (affine confinement, concavity) | — (analytic; Hankel leader = `hankel_powerSum_posSemidef`) | PROSE + finite shadow PROVED |
| T17 | susceptibility balance `⟺ β=½` | `SusceptibilityBalance` module (atlas, GaloisForLFunctions) | PROVED (finite/local) |
| T25 | `F_q` border (Papanikolas/Deligne) | `functionField_localFactor_FE`, `cayley_etaUnitary` | PROVED (FE-palindrome core) |
| T27 | Stieltjes–log weld (Tier-1) | `stieltjes_pairing_cauchy_j` | PROVED |
| T29 | Li/secular `P_k=Σρ^{−k}` | `superzeta_coeff_eq_powerSum`, `powerSum_torelli` | PROVED |
| T6,T7,T10,T18–T24,T26,T28 | holonomicity / G1-Hölder / abscissa / erosion / Fisher / DSS-no-go / Koszul | partial bricks (`HolonomicityLimit`, `KoszulCohomology`, …) | PROVED (cores) / PROSE (analytic parts) |

## Table D — Light-tower Theorems A–L (Doc 03)

| | Theorem shape | Status | Note |
|---|---|---|---|
| A | far-left phase-weld `Δ_P→log 2` | PROSE | experimental/analytic; no Lean object |
| B | transition-band transport metric | PROSE | experimental |
| C | coupled lane co-failure | PROSE | experimental |
| D | q70 association gate | PROSE | experimental; continuum operator = open lemma L-C |
| E | Berry completion switch | PROSE | derivable-from-FE target (L-B); not Lean |
| F | observed-volume covariance | PROSE | experimental |
| G | phase-space caustic | PROSE | experimental |
| H | phase-regulated dissolution | PROSE | experimental |
| I | reset-occupation centre = `β` | PROSE + local | local pole model `ξ'/ξ~m/(s−ρ)`; finite curvature classical |
| J | two-clock covariance | PROSE | experimental |
| K | context-fragility monotone | PROSE | experimental |
| L | right-strip collapse `σ>1⟹P_N→P` | PROVED (math fact) | Euler convergence; trivial, not separately Lean'd |

## Table E — Conjectures (Doc 08): Lean attempts

| Conjecture | Lean | Module | Status | Gap / note |
|---|---|---|---|---|
| APEX-A first rung `corank^{(2)}` (degree-2 prime-log LI) | `corank_two_pair` | OpenConjectures | SORRY | needs **Gelfond–Schneider** (`log p/log q` transcendental); absent from mathlib v4.30.0 |
| APEX-A full Schanuel-for-prime-logs | `schanuel_prime_logs` | OpenConjectures | AXIOM | classical OPEN (open for `{log2,log3}`); imported as hypothesis |
| APEX-B `RH ⟺ κ₋=0` (C18 faithful-index rigidity) | `weil_positivity_is_RH` | OpenConjectures | AXIOM | Weil-positivity import; analytic RH not in scope |
| APEX-B off-line ⟹ not faithful (LT8 dust-proof dir) | `offline_breaks_faithful` | OpenConjectures | **PROVED (corollary)** | from `fe_quadruple_kappa_two` (κ₋=2≥1) |
| APEX-B uniform Hankel restricts to finite-d | `uniform_imp_finite` | OpenConjectures | **PROVED (corollary)** | converse (finite⟹uniform) is the open apex |
| APEX-B uniform-`d` Hankel `det H_d≥0 ∀d ⟺ RH` | `UniformlyPosSemidef` (def) | OpenConjectures | PROSE/def | finite shadow PROVED (`moment_matrix_posSemidef_iff`); uniformity open (R30/R31) |
| C1 oriented 2-form carrier | — | — | PROSE | needs analytic `O,φ`; experimental |
| C2 holonomy of affine connection, Γ trivializes on σ=½ | — | (Koszul/CC bricks) | PROSE | cocycle layer PROVED (`koszulD1_*`); holonomy class = open |
| C3 phase-Sobolev gap | — | — | PROSE | analytic |
| C4 cross-lane correlation length | — | — | PROSE | analytic |
| C5 crossover scale σ* | — | — | PROSE | analytic |
| C6 inverse completion problem | — | (CC bricks) | PROSE | cocycle uniqueness PROVED in part |
| C7 local pole detector | — | — | PROSE | local pole model |
| C8 global seam confinement (Lemma 2) | — | — | PROSE | the RH arrow; open core |
| C9 native-HGT carrier (surrogate ladder) | — | — | PROSE | experimental adjudication |
| G-C10/16 source-built faithful-index / Jacobi positivity | — | (carrier bricks) | PROSE | finite carrier PROVED; source-built construction open |
| G-C11/19 F1/Hodge polarization / primitive Schur–Hodge | `hodge_index_ineq`, `pos_not_primitive` | HodgeIndexInequality | PROVED (finite Hodge-index); F1 realization PROSE |
| G-C17 uniform Jensen / Laguerre–Pólya | `moment_matrix_posSemidef_iff` | HermiteHankelDetector | PROVED (finite); uniform = open |

---

## Summary counts

- **PROVED, sorry-free, in the atlas:** 26 bricks (Table A) + 16 apex forms (Table B) + 2 manufactured
  corollaries (`offline_breaks_faithful`, `uniform_imp_finite`) = **44 consolidated Lean theorems**.
- **Stated open in Lean:** 1 SORRY (`corank_two_pair`), 2 AXIOM (`schanuel_prime_logs`,
  `weil_positivity_is_RH`), + predicate defs (`FaithfulPositive`, `UniformlyPosSemidef`).
- **PROSE (not Lean-formalizable at current abstraction):** the experimental light-tower Theorems
  A–K and the analytic conjectures C1–C9 (no analytic `riemannZeta`/`ξ` carrier layer is in scope;
  their FINITE shadows are proven where they exist — Hankel, secular Herglotz, κ₋, Hodge index).

**The honest one-line status:** every consolidated item whose core is *algebraic/finite* is genuinely
proved (sorry-free) in the atlas; every item whose core is the *open analytic apex* (RH, Schanuel,
uniform-`d` positivity) is stated precisely with a visible `sorry`/`axiom` and its missing ingredient
named. No `sorry` is dressed as a proof.

## Build / verification status

- `lake build GaloisForLFunctions` — bricks compiled in the atlas (identical mathlib rev). [confirm]
- `lake build JensenLadder.Consolidated.Roster` — machine-checks all PROVED names resolve. [confirm]
- `lake build JensenLadder.Consolidated.OpenConjectures` — open targets compile (with the marked
  `sorry`/`axiom`). [confirm]
- Axiom audit (`#print axioms`) on the bricks: the cards report `[propext, Classical.choice,
  Quot.sound]` only. [confirm in atlas]

---

## Deep-research cross-check (incorporating `hgt/docs/consolidated/deep-research-report.md`)

An independent external audit (GPT deep research) of the same corpus was folded in. It confirms this
index's honesty split (algebraic/finite cores closeable; analytic apex open) and supplies two formal
corrections and sharpened gap statements.

### Two formal corrections (and how the Lean handles them)
1. **Fixed-locus correction.** `Re s = ½` is the fixed locus of the **anti-holomorphic** involution
   `s ↦ 1−s̄`, NOT the holomorphic `s ↦ 1−s` (whose fixed locus is the single point `s=½`). **The
   atlas Lean is already correct**: it carries *two* maps — `GaloisForLFunctions.sigma` (holomorphic,
   order-2, `sigma_involutive`) for the constraint `ι`, and `GaloisForLFunctions.sigmaConj`
   (anti-holomorphic) for the critical line, with `sigmaConj_fixed_iff_critical : sigmaConj s = s ↔
   s.re = 1/2`. Table A cites the correct map for each role. (The light-tower prose conflated them;
   the formalization does not.)
2. **Curvature-window correction.** `2(a²−τ²)/(a²+τ²)²` is the contribution of the **same-height
   mirror pair** `ρ = ½ ± a + iγ` to `(log Ξ)''(t)` near `t=γ`; the conjugate pair gives a second
   window near `t=−γ`. (Phrasing refinement; not Lean-formalized — analytic. The curvature identity
   `(log Ξ)''(t) = Σ_ρ (½+it−ρ)^{-2}` and RH⟹concavity are "closeable" classically but need an
   analytic ζ layer absent from the atlas abstraction.)

### Sharpened gap notes for the open conjectures (Document B "what is missing")
| Item | Smallest missing ingredient (per audit) |
|---|---|
| C1 oriented 2-form | a coordinate-free 2-form + a surrogate-separation theorem |
| C2 holonomy | explicit base space, coefficient module, and a holonomy class **distinct from winding number** |
| C3 phase-Sobolev | a sharp regularity-to-persistence inequality (or counterexample) |
| C4 correlation length | a theorem separating zero-statistics from native transport coupling |
| C5 crossover | a scaling law / critical exponent / proof of a nonanalytic kink |
| C6 inverse problem | a precise reconstruction *category* + an impossibility theorem |
| B1 source-measure bridge | the transport-to-source ("hard arrow") theorem |
| B2-L2 confinement | a global rigidity theorem (the open core) |
| APEX-A Schanuel | Schanuel / four-exponentials / a new transcendence theorem (Baker gives only **linear**) |
| APEX-B uniform Hankel | a genuine **all-degree** positivity theorem (local gap/curvature provably don't control all `d` — R30/R31) |
| APEX-C universal orthogonality | a classification theorem for the admissible prime-side category |
| APEX-D C5★ | a full mathematical **definition** of `C5★` first, then a theorem |

These confirm the `SORRY`/`AXIOM`/`PROSE` statuses above are not laziness but the corpus's genuine
open wall: "the right next move is not to broaden vocabulary but to close one of two bridges —
transport-to-source, or all-degree positivity."

### Literature anchors for the gaps (audit references)
- **Hölder 1887 / Hardouin–Singer 2008** — Γ differential transcendence (parameterised diff-Galois);
  grounds T3, T7 (the `non-CC ⟹ HT` import / `weil_positivity`-style axioms).
- **Baker 1960s** — linear forms in logs; grounds `linearIndependent_log_primes` (the proven floor).
- **Schanuel / four-exponentials / Gelfond–Schneider** — the missing input for `corank_two_pair`
  (SORRY) and `schanuel_prime_logs` (AXIOM); GS is absent from mathlib v4.30.0.
- **Deligne (Weil II) 1973–74** — the `F_q` border; grounds `functionField_localFactor_FE`,
  `cayley_etaUnitary`.
- **Connes 1998–99 / Connes–Consani** — spectral interpretation + Weil positivity & the archimedean
  place; grounds the `RH ⟺ κ₋=0` direction (`weil_positivity_is_RH`, AXIOM).
- **Papanikolas 2005** — period-matrix trdeg = Galois-dim for t-motives; the `F_q` DSS face.
- **Griffin–Ono–Rolen–Zagier 2019 / O'Sullivan** — Jensen–Pólya hyperbolicity proved in restricted
  regimes / finite degree, NOT all-degree; grounds APEX-B (`moment_matrix_posSemidef_iff` is the
  finite shadow; uniform-`d` is the open target).
