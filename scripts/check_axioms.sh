#!/usr/bin/env bash
# Axiom + sorry audit for the JensenLadder RH-equivalences / no-go library.
#
# Verifies that a curated set of HEADLINE theorems — spanning the four
# categories of the library (the mathlib-RH reduction spine, the carrier
# equivalences, the no-go certificates, and the unconditional analytic
# bricks) — each depend on exactly the three standard mathlib axioms
#   [propext, Classical.choice, Quot.sound]
# and that the source tree contains no `sorry`.
#
# Fails (exit 1) if any headline theorem carries an extra axiom (e.g.
# `sorryAx`), if any headline name is missing/misspelled, or if a real
# `sorry` token appears anywhere in the tree.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")/../formal" && pwd)"
command -v lake > /dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"

# --- curated headline theorems (full names) --------------------------------
HEADLINES=(
  # spine: mathlib's official RiemannHypothesis <-> regular Xi zeros real
  "JensenLadder.RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real"
  "JensenLadder.RHReduction.riemannXi_even"
  "JensenLadder.RHReduction.riemannXiRegularZero_neg"
  # carrier equivalence lattice: RH <-> existence of a faithful structure
  "JensenLadder.HodgeIndexCarrier.hasFaithfulHodgeIndexCarrier_iff_riemannHypothesis"
  "JensenLadder.HodgeIndexCarrier.hasFaithfulHodgeIndexCarrier_iff_hasFaithfulArithmeticSiteCarrier"
  "JensenLadder.ArithmeticSiteCarrier.hasFaithfulArithmeticSiteCarrier_iff_riemannHypothesis"
  "JensenLadder.GeometricSquareRootCarrier.hasFaithfulGeometricSquareRootCarrier_iff_hasFaithfulHodgeIndexCarrier"
  "JensenLadder.FredholmSquaredCarrier.hasFaithfulFredholmSquaredCarrier_iff_riemannHypothesis"
  "JensenLadder.SpectralRealization.nonempty_spectralRealization_iff_riemannXi_zeros_real"
  # no-go certificates: proven obstructions ruling out naive strategies
  "JensenLadder.DHMultiplicityFakeGate.not_coprimeMultiplicative_of_DHPattern236"
  "JensenLadder.DHMultiplicityFakeGate.not_totallyMultiplicative_of_DHPattern236"
  "JensenLadder.ScatteringParityNoGo.logDeriv_eq_zero_of_scattering_eq_xi"
  "JensenLadder.PrimeLocalNoGo.not_forall_nonnegative_diagonal_add_oneSidedPrimeKernel_of_delta_lt_threshold"
  "JensenLadder.ResolutionWall.not_forall_certificate_margin_of_uniform_floor_arbitrarily_small_margins"
  # no-go certificates: operator-algebraic / universality family
  "JensenLadder.AmenabilityNoGo.no_eulerBlind_reality_gate"
  "JensenLadder.ModularQuotientNoGo.modular_ab_hom_to_int_trivial"
  "JensenLadder.PrimeQuarantineTraceNoGo.quarantine_trace_zero_of_weight_gt_one"
  # unconditional analytic bricks about the completed zeta
  "JensenLadder.RvMXiEntire.xiE_zero_iff_zeta_zero"
  # finite Hodge -> Weil positivity bridge
  "JensenLadder.HodgeWeilBridge.quadraticForm_eq_arch_sub_prime"
)

SCRATCH="$(mktemp -t jl-axcheck-XXXXXX).lean"
trap 'rm -f "$SCRATCH"' EXIT
{
  # JensenLadder pulls the carrier lattice, no-go and reduction modules into
  # scope; the analytic bricks live outside the aggregator's import closure
  # and are imported explicitly.
  echo "import JensenLadder"
  echo "import JensenLadder.RvMXiEntire"
  for name in "${HEADLINES[@]}"; do
    echo "#print axioms ${name}"
  done
} > "$SCRATCH"

cd "$FORMAL_DIR"
# Tolerant capture: an unknown/misspelled headline name makes `lean` exit
# nonzero; we want that surfaced as a per-name FAIL below, not an early abort.
OUT="$(lake env lean "$SCRATCH" 2>&1 || true)"
echo "$OUT"
echo "----------------------------------------------------------------"

# Lean wraps long axiom lists across lines; normalize whitespace so each
# "'name' depends on axioms: [..]" record sits on a single logical line.
NORM="$(printf '%s' "$OUT" | tr '\n' ' ' | sed 's/  */ /g')"
EXPECTED="[propext, Classical.choice, Quot.sound]"

FAIL=0
for name in "${HEADLINES[@]}"; do
  if printf '%s' "$NORM" | grep -qF "'${name}' depends on axioms: ${EXPECTED}"; then
    echo "OK   ${name}"
  else
    echo "FAIL ${name}  (missing, misspelled, or extra axiom)" >&2
    FAIL=1
  fi
done

if printf '%s' "$OUT" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx present in a headline theorem" >&2
  FAIL=1
fi

# Global sorry sweep over the source tree (exclude comments / doc lines).
if grep -rnE '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' --include='*.lean' \
    JensenLadder/ JensenLadder.lean \
    | grep -vE '^\S+:[0-9]+:\s*(--|/-|`| \*)' \
    | grep -vF 'no `sorry`'; then
  echo "FAIL: sorry token found in tree" >&2
  FAIL=1
fi

echo "----------------------------------------------------------------"
if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM AUDIT FAILED" >&2
  exit 1
fi
echo "OK: ${#HEADLINES[@]} headline theorems axiom-clean (${EXPECTED}), zero sorries."
