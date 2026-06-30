/-
# Consolidated Research → Lean: PROVEN roster (machine-checked index)

This module is the machine-checkable half of the consolidation formalization
(`docs/CONSOLIDATED_LEAN_INDEX.md`). Every `#check` below names a theorem that is **already
proven, sorry-free** in this project — either in the `GaloisForLFunctions` library (the
hypertranscendence / weld / corank / orbit / carrier bricks, ported from `hgt/formal`,
identical mathlib `v4.30.0`) or in the `JensenLadder` library (the RH-side apex forms native to
this atlas: Hodge index, faithful/measured, secular Herglotz, Hankel hierarchy, Li, Cayley).

If this file builds, every Lean name claimed "PROVED" in the index resolves and type-checks.
The open conjectures and the items that are only stated (not proved) live in
`JensenLadder.Consolidated.OpenConjectures`, never here.

Cross-reference: consolidated docs `publications/hgt/docs/consolidated/{03,07,08,09}-*.md`.
-/
import GaloisForLFunctions
import JensenLadder.HodgeIndexInequality
import JensenLadder.FaithfulMeasuredDichotomy
import JensenLadder.SecularHerglotz
import JensenLadder.BezoutianResidue
import JensenLadder.HermiteHankelDetector
import JensenLadder.LiCriterionDisk
import JensenLadder.CayleyUnitaryBridge
import JensenLadder.SecularRealRoots

namespace JensenLadder.Consolidated.Roster

/-! ## LT2 / LT3 — the weld, the seam, the constraint (Doc 07 §1 T1–T3, §2 bricks)

`linearIndependent_log_primes` is the proven LINEAR floor `corank = ∞` (Baker); `sigma_involutive`
and `sigmaConj_fixed_iff_critical` are the order-2 constraint `ι` and its fixed locus `Re = ½`
(constraint-not-flow, fe-constraint-critical-line-fixed-locus); `boundaryUnitNormalize_…` is
`|p^{-s}| = p^{-1/2} ⟺ Re(s) = ½`. -/
#check @GaloisForLFunctions.linearIndependent_log_primes
#check @GaloisForLFunctions.logPrime_no_rat_relation
#check @GaloisForLFunctions.finitePrimeLogAnnihilator_eq_singleton
#check @GaloisForLFunctions.sigma_involutive
#check @GaloisForLFunctions.sigmaConj_fixed_iff_critical
#check @GaloisForLFunctions.boundaryUnitNormalize_norm_eq_one_iff
#check @GaloisForLFunctions.primeLogFrequency_eq_zero_iff

/-! ## LT2 — the archimedean generator A(s) = ∂_s log Γ∞, Fourier-diagonal (T11–T13) -/
#check @GaloisForLFunctions.gammaReal_shift_two
#check @GaloisForLFunctions.deriv_archimedeanPrimeMode
-- corank-no-collapse: adjoining ∂_s leaves the prime-log span rank unchanged ("F₁ is NOT ∂_s")
#check @GaloisForLFunctions.primeLogFullSpan_insert_archimedean_eq
#check @GaloisForLFunctions.primeLogFiniteSlice_finrank_with_archimedean_unbounded

/-! ## Transport as holonomy / cocycle (Doc 02 §5; T2/T3) — Koszul cocycle + CC-gauge -/
#check @GaloisForLFunctions.koszulD1_eq_zero_iff_additiveCocycle
#check @GaloisForLFunctions.koszulD1_koszulD0_eq_zero
#check @GaloisForLFunctions.ccGaugeMultiplier_eq_const
#check @GaloisForLFunctions.orbitDegree_intShiftCoboundary

/-! ## Source-B has no polarization (T8/T9 orthogonality) — rank-one dual-multiplier obstruction -/
#check @GaloisForLFunctions.rankOne_noSelfDualMultiplier_of_sq_ne_one

/-! ## The F_q border: Weil FE L-polynomial palindrome (T25) -/
#check @GaloisForLFunctions.functionField_localFactor_FE

/-! ## LT8 — the FAITHFUL off-line index κ₋ (T5, T14, T15): κ₋ = #off-line pairs (Sylvester),
one off-line zero ⟹ κ₋ = 2, and the Krein–Langer inertia bounds. -/
#check @GaloisForLFunctions.multiPair_carrier_exact_neg_inertia
#check @GaloisForLFunctions.fe_quadruple_kappa_two
#check @GaloisForLFunctions.neg_inertia_le_of_posSemidef
#check @GaloisForLFunctions.sigNeg_le_one_of_add_sq_nonneg

/-! ## Secular / superzeta reconstruction (T29) — P_k = Σ_ρ ρ^{-k}; Newton power-sum Torelli -/
#check @GaloisForLFunctions.superzeta_coeff_eq_powerSum
#check @GaloisForLFunctions.powerSum_torelli
#check @GaloisForLFunctions.spectralTorelli_faithful

/-! ## Stieltjes–log weld pairing (T27) + Sato–Tate orthonormality (Satake 2nd moment ≥ 0) -/
#check @GaloisForLFunctions.stieltjes_pairing_cauchy_j
#check @GaloisForLFunctions.satoTate_orthonormal

/-! ## RH-side apex forms native to this atlas (JensenLadder) — the positivity axis APEX-B.
faithful vs measured (LT1, the dust-proof distinction); secular Herglotz = m_ξ ∈ N₀ direction;
Hodge index signature; Hankel/moment hierarchy (det H_d ≥ 0 leader); Li criterion; Cayley unitary. -/
#check @JensenLadder.faithful_imp_measured
#check @JensenLadder.measured_not_imp_faithful
#check @JensenLadder.secular_herglotz
#check @JensenLadder.cauchy_pole_not_herglotz
#check @JensenLadder.herglotz_real_level
#check @JensenLadder.hodge_index_ineq
#check @JensenLadder.pos_not_primitive
#check @JensenLadder.bezout_eq_residue_gram
#check @JensenLadder.hankel_powerSum_posSemidef
#check @JensenLadder.moment_matrix_posSemidef_iff
#check @JensenLadder.cofactor_gram_posDef_iff
#check @JensenLadder.secular_roots_real
#check @JensenLadder.secular_strictMono
#check @JensenLadder.cayley_etaUnitary
#check @LiCriterionDisk.li_coefficient_nonneg_of_unit_modulus
#check @LiCriterionDisk.norm_one_sub_inv_lt_one_iff

end JensenLadder.Consolidated.Roster
