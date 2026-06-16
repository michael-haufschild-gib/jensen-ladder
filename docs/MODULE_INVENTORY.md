# rh-formal-atlas — module inventory

Companion to the preprint `docs/preprint/main.tex`. Every source module of
`formal/JensenLadder/` is listed once, under its primary role. Verified this
pass: `lake build` green (128 source modules, 8602 jobs), zero `sorry`, no added
`axiom`; 16 headline theorems confirmed axiom-clean
(`[propext, Classical.choice, Quot.sound]`) by `scripts/check_axioms.sh`.

Roles: **S** reduction spine · **L** equivalence-lattice carrier · **N** no-go
certificate · **P** finite positivity algebra · **A** unconditional analytic
brick · **T** deterministic analytic toolkit / squared-determinant machinery.

> Scope (load-bearing): no module instantiates a faithful carrier. The library
> proves reductions, equivalences, and obstructions — **not** RH. Theorem M is
> proven separately and does **not** prove RH by itself.

## S — Reduction spine (mathlib RH → regular Ξ-zero reality)

| Module | Role |
|---|---|
| `RHReduction` | `RiemannHypothesis ⟺ (∀ regular Ξ-zero, real)`; FE = evenness (`riemannXi_even`); zero-set `z↦−z` symmetry. Unconditional, axiom-clean. |
| `XiJensen` | Convention layer: Ξ Jensen/Taylor sections in the symmetric (squared) variable. |
| `Basic` | Shared definitions. |

## L — Equivalence lattice: RH ⟺ ∃ faithful carrier

Each module proves `riemannHypothesis_of_faithfulRows`,
`not_faithfulRows_of_nonrealRegularXiZero` (falsifier), and `…_do_not_supply_…`
non-supply lemmas; carriers are linked by kernel-checked `iff`s.

| Module | Carrier / equivalence (open content = the faithful rows) |
|---|---|
| `HodgeIndexCarrier` | RH ⟺ faithful Hodge-index carrier ⟺ arithmetic-site carrier |
| `ArithmeticSiteCarrier` | RH ⟺ faithful arithmetic-site carrier (Lefschetz/Weil-trace rows) |
| `GeometricSquareRootCarrier` | nonnegative Weil form ⟺ abstract square root; ⟺ Hodge-index carrier |
| `DeningerCarrier` | RH ⟺ polarized faithful dictionary (flow/determinant interface) |
| `DeningerFlowUnitary` | flow-unitarity variant of the Deninger dictionary |
| `FriedDeningerTorsionCarrier` | Fried–Deninger torsion variant of the dictionary |
| `MomentProblemCarrier` | RH ⟺ faithful moment-problem carrier ⟺ spectral realization |
| `SpectralRealization` | RH ⟺ ∃ (regular) spectral realization of the Ξ-zeros |
| `SpectralReflection` | RH ⟺ ∃ FE-symmetric (reflected) regular spectral realization |
| `ComplexSpectralDeterminantCarrier` | complex spectral-determinant realization boundary |
| `UnitaryCokernelCarrier` | unitary-cokernel realization boundary |
| `FredholmSquaredCarrier` | RH ⟺ faithful Fredholm-squared carrier ⟺ nonnegative squared support |
| `SquaredVariablePullback` | reality from nonnegative squared support / approximation |
| `PrimeCepstrumHankelCarrier` | prime-cepstrum Hankel realization (feeds Fredholm-squared) |
| `MorseCriterion` | RH ⟺ no negative modes ⟺ nonnegative spectral bottom |
| `MorseDeningerBridge` | no negative modes ⟺ polarized faithful dictionary ⟺ RH |
| `BochnerTopRoute` | RH ⟺ nonpositive "top" (Bochner simple-top calibration) |
| `MagicInterpolationBridge` | magic-interpolation data ⟹ RH (+ falsifier); Viazovska-style certificate target |
| `ModelToXiTransfer` | model endpoint (Theorem M) + transfer row + Jensen gate ⟹ RH |
| `PolyaSchurTransfer` | transfer row as a Pólya–Schur multiplier sequence (`M ∈ LP`) |
| `W3InnerFactor` | RH-equivalent hypothesis: operator-norm < 1 ⟹ no fixed eigenvalue |
| `LiCriterionDisk` | Li's criterion in `w = 1 − 1/ρ`: coefficient positivity from unit-modulus |
| `TruncationLimitCarrier` | exhaustive truncation family ⟹ realization ⟹ RH |
| `SpectralPollutionFreeLimit` | pollution-free spectral limit ⟹ RH |
| `CVSSpectralRoute` | Connes–van Suijlekom: simple-even ground states + convergence ⟹ RH |
| `CVSGapPreservation`, `CVSKatoWeyl`, `CVSFiniteGapScreen`, `CVSMarginalLimit` | gap/Kato/limit handoffs for the C–vS route |
| `CCMGroundStateRoute`, `CCMGroundStateError` | CCM ground-state route + its error/floor handoff |
| `OddMorseCertificate` | odd-sector Morse certificate handoff |
| `DeterminantHurwitzRoute` | `det_reg`→Ξ determinant route (Hurwitz convergence consumer) |
| `SquaredDeterminantApproximation`, `…ZeroTransfer`, `…SpectralProduct`, `…PairedSpectralProduct`, `…HurwitzBridge` | squared-determinant zero-shadowing route to RH |
| `MeyerForkASquaredDeterminant` | Meyer fork-A squared-determinant boundary |
| `DiagonalFredholmProduct` | diagonal Fredholm product surrogate (completeness ⟹ RH) |
| `BurnolCriticalSystems` | Burnol critical complete/minimal systems (exactness = criticality) |

## N — No-go certificates (finite, unconditional obstructions)

| Module | What is proved |
|---|---|
| `DHMultiplicityFakeGate` | Davenport–Heilbronn pattern is not (coprime/totally) multiplicative |
| `FiniteMultiplicityVisibilityNoGo` | a finite visible predicate cannot force coprime multiplicativity |
| `FiniteMixedLogVisibilityNoGo` | finite mixed-log data cannot force the product relations |
| `FiniteEulerProductMixedLogGate` | mixed-log cancellation ⟺ product (Euler-coupling) relations; DH violates it |
| `FiniteCarrierNoGo` | a finite spectrum cannot represent infinitely many distinct zeros |
| `PrimeLocalNoGo` | one-sided prime-local kernel negative below threshold ⟹ local positivity fails |
| `PrimeLocalHodgeNoGo` | one-sided prime-local data admits a negative Hodge vector |
| `ScatteringParityNoGo` | even scattering log-derivative cannot equal odd Ξ — closes the ratio class |
| `ResolutionWall` | uniform floor + arbitrarily small margins ⟹ contradiction (no margin) |
| `BAH1Quadratic`, `BAH1PrimeRow` | residual-margin impossibility; finite prime-row scale-lock algebra |
| `CVSKatoSmallNoGo` | Kato-smallness fails under critical gap collapse |
| `AdversarialSignTwistNoGo` | adversarial sign-twist forces a negative direction unless budget ≤ arch |
| `AbsoluteBudgetFakeFamilyBlindness` | absolute-budget certificates are blind to sign-retwisted fakes |
| `DeterminantNormalizationNoGo` | post-hoc scalar normalization cannot repair `det_reg` |
| `SpectralFaithfulnessGap` | an off-axis regular zero ⟹ the squared spectrum is not faithful |
| `SchurStarSharpness` | arch < response budget ⟹ an explicit negative form (sharpness/falsifier) |
| `SymmetryProtection` | the no-margin wall is symmetry-protected (RH-agnostic moment identities) |

## P — Finite positivity algebra (the square-root / domination mechanics)

| Module | Role |
|---|---|
| `HodgeWeilBridge` | finite semilocal Weil form = arch − Σ prime; Hodge realization ⟹ PSD; neg vector ⟹ no realization |
| `PrimitiveHodgeWeilEngine`, `PrimitiveHodgeWeilCalibration` | primitive Hodge–Riemann engine for finite Weil forms |
| `HodgeSignatureBabyCarrier` | signature `(1,·)` toy: primitive self-intersection ≤ 0 |
| `PrimeDominationBabyCarrier` | off-diagonal-dominated block is PSD (exact square) |
| `GraphLaplacianBabyCarrier` | rooted incidence energy is an exact square; off-diagonal dominated |
| `RowDiagonalDominationCarrier`, `GlobalDominationReduction` | row/global missing-diagonal domination ⟹ nonnegativity |
| `DiagonalBudgetSharpness` | completed block PSD ⟺ |coupling| ≤ diagonal (sharp) |
| `SchurStarDominationCarrier`, `SchurStarAssemblyCarrier` | Schur-star leaf energy; response budget ≤ arch ⟹ nonneg form |
| `ResidualSchurSelector` | finite residual Schur complement / transverse-mass algebra |
| `CCMFiniteWeil` | finite semilocal Weil matrix interface (arch + prime parts) |
| `CCMRankOne`, `CCMQuotient` | finite rank-one scaling perturbation + boundary quotient |
| `CCMFrobeniusBound`, `CCMPerturbationBound`, `CCMFiniteKatoBridge` | Frobenius/row/Kato-radius bounds for the finite CCM perturbation |
| `EulerLoadedPrimitiveProjection` | Euler-loaded projection gate (Schur-syntax rows do not supply Euler-loaded rows) |
| `ChiralDiracSquare` | chiral-Dirac determinant perfect-square; skew-adjoint eigenvalues `Re=0` |
| `ChiralMomentPSD`, `ChiralStieltjesTrace` | finite chiral moment Hankel PSD; Stieltjes/Fredholm trace identities |
| `ChiralMomentReconstruction`, `ChiralSourceMomentGate`, `ChiralSourceTraceReconstruction`, `ChiralExplicitFormulaSource`, `PrimeCepstrumHankelCarrier` | chiral source→moment→determinant reconstruction chain (with non-supply lemmas) |

## A — Unconditional analytic bricks (real ζ/ξ content)

| Module | Role |
|---|---|
| `RvMXiEntire` | entire completion `xiE`; nonneg divisor; `xiE(s)=0 ⟺ ζ(s)=0` on the strip (Riemann–von Mangoldt) |
| `RvMXiLink` | coordinate link: s-variable `xiE` = z-variable `xiEntire` |
| `ZeroCountingN` | zero-counting function `N(T)` (finite, monotone) |
| `XiOrderBound` | order-1 growth bound for the carrier Ξ |
| `XiZeroCounting` | Jensen zero-counting bound; `Σ 1/‖u_ρ‖` summability ingredient |
| `W1DensityNevanlinna` | Nevanlinna bricks toward `Σ_ρ 1/(¼+γ²) < ∞` |
| `CompletedZetaStripBound` | vertical-strip bound for the entire completed zeta |
| `XiEntireEven` | FE evenness of the entire Ξ (HurwitzBridge namespace) |
| `HurwitzRealRootedLimit` | from-scratch argument principle + nowhere-zero Hurwitz; `det_reg→Ξ ⟹ RH` |
| `CanonicalProductGenusOne`, `CanonicalProductFactorZeros`, `CarrierCanonicalProduct` | genus-0/1 Weierstrass canonical products and factor zeros |
| `GenusOneDeterminantControl` | det ↔ eigenvalue bridge (forward half) |
| `ModelTuranRatio` | closed form for the Theorem-M model Turán ratios |

## T — Deterministic analytic toolkit / squared-determinant machinery

| Module | Role |
|---|---|
| `Sturm` | sign-change root counting; splits-of-sign-changes certificate |
| `CauchyTransfer`, `LogTransfer`, `MomentLogError` | deterministic Cauchy / log / moment-log transfer cores |
| `E1K`, `DerivativeBasepointConvergence` | contraction-mapping fixed point; derivative+basepoint convergence |
| `IntegrandHolomorphy`, `AffineContour`, `CorridorGeometry`, `ContourLegality` | steepest-descent SD-C0..C3 holomorphy / contour / corridor pieces |
| `SDCMargin`, `SDCertificate` | SD-C3 margin from certified connector/tail bound; SD-C end-to-end capstone |
| `SquaredDeterminantFinite`, `SquaredDeterminantGauge` | finite squared-determinant multiplicativity / gauge cancellation |
| `T1Phase`, `T2Edge`, `SuzukiPhase` | T1 phase-margin, T2 Airy/Langer edge, Suzuki phase-parity consumers |
| `C2PComparison`, `C2PLowerRow`, `C2PResponseNorm`, `C2PSuzukiMass`, `C2PFullCertificate`, `MomentTraceBridge`, `PacketForce` | C2P comparison-certificate interfaces and Row-P2 exclusion core |
| `StructureTheorem` | structure-theorem consumer: residual → Lehmer-scale confinement |

## Root

`JensenLadder.lean` aggregates the lattice / no-go / reduction modules (the
analytic bricks `RvMXiEntire`, `RvMXiLink`, `ZeroCountingN`, `XiOrderBound`,
`XiZeroCounting`, `W1DensityNevanlinna`, `CompletedZetaStripBound`,
`XiEntireEven` build under `lake build` but sit outside the aggregator's import
closure; `scripts/check_axioms.sh` imports them explicitly).
