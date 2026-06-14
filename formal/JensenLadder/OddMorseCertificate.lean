import JensenLadder.MorseCriterion

/-!
# Odd-sector Morse certificate handoff

This module packages the final Lean handoff shape for the Yoshida/Suzuki
odd-sector route.

There are four deliberately separate interfaces:

* `DirectOddSufficientData` records the one-way Yoshida/Suzuki odd-sector
  sufficiency criterion: nonnegativity of a calibrated odd-sector bottom at
  every scale implies `RiemannHypothesis`.
* `DirectOddProofData` records the stronger two-way version, useful when the
  converse row is also available.
* `ProofData` records the side-hypothesis global-Morse/parity-split route:

* a direct Morse/RH criterion,
* a parity split of the Morse index,
* an odd-sector bottom calibration,
* protection of the even sector from negative modes.
* `ParityBottomProofData` records the fully calibrated parity-bottom route:

* a direct Morse/RH criterion,
* a parity split of the Morse index,
* odd-sector and even-sector bottom calibrations,
* nonnegativity rows for both calibrated bottoms.

The distinction matters: even-sector protection in the global-Morse package is
an open analytic row, not something discharged by the odd-function criterion;
the fully calibrated handoff makes that row visible as an even-bottom
nonnegativity obligation.
This file does not construct the zeta family, prove the Yoshida/Suzuki
criterion, prove even-sector protection, or prove any odd/even bottom
nonnegativity row.

Theorem M is proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace OddMorseCertificate

open MorseCriterion

universe u

/-- A two-region cover of a scale parameter.

The intended use is the Suzuki/Yoshida split between a small-`a` theorem and
the remaining large-tail positivity problem.  This is purely bookkeeping: the
cover itself proves no sign information. -/
structure ScaleCover (Scale : Type u) where
  small : Scale → Prop
  large : Scale → Prop
  cover : ∀ a : Scale, small a ∨ large a

namespace ScaleCover

/-- The ordered cutoff cover `a ≤ cutoff` or `cutoff ≤ a`. -/
def ofCutoff {Scale : Type u} [LinearOrder Scale] (cutoff : Scale) :
    ScaleCover Scale where
  small a := a ≤ cutoff
  large a := cutoff ≤ a
  cover a := le_total a cutoff

end ScaleCover

/-- Bottom nonnegativity restricted to a region of scales. -/
def BottomNonnegativeOn {Scale : Type u}
    (bottom : Scale → ℝ) (region : Scale → Prop) : Prop :=
  ∀ a : Scale, region a → 0 ≤ bottom a

/-- A regional lower-to-upper bottom comparison. -/
def BottomLeOn {Scale : Type u}
    (lower upper : Scale → ℝ) (region : Scale → Prop) : Prop :=
  ∀ a : Scale, region a → lower a ≤ upper a

/-- Regional nonnegativity transfers across a regional bottom comparison. -/
theorem bottomNonnegativeOn_of_leOn
    {Scale : Type u} {lower upper : Scale → ℝ} {region : Scale → Prop}
    (hlower : BottomNonnegativeOn lower region)
    (hle : BottomLeOn lower upper region) :
    BottomNonnegativeOn upper region := by
  intro a ha
  exact le_trans (hlower a ha) (hle a ha)

/-- Regional bottom nonnegativity over a two-region cover assembles the global
all-scale bottom row. -/
theorem nonnegativeBottom_of_scaleCover
    {Scale : Type u} {bottom : Scale → ℝ}
    (cover : ScaleCover Scale)
    (hSmall : BottomNonnegativeOn bottom cover.small)
    (hLarge : BottomNonnegativeOn bottom cover.large) :
    NonnegativeBottom bottom := by
  intro a
  rcases cover.cover a with hsmall | hlarge
  · exact hSmall a hsmall
  · exact hLarge a hlarge

/-- One-way Lean-facing proof data for the Yoshida/Suzuki odd-function route.

Supplying this structure for a concrete zeta Weil-form family is the analytic
sufficiency theorem: the forward field is the load-bearing result that
odd-sector bottom nonnegativity at every scale implies RH.  This is the weaker
interface needed for an RH certificate; it does not ask for the converse row. -/
structure DirectOddSufficientData where
  Scale : Type u
  oddBottom : Scale → ℝ
  riemannHypothesis_of_nonnegativeOddBottom :
    NonnegativeBottom oddBottom → RiemannHypothesis

namespace DirectOddSufficientData

/-- The remaining positivity row for one-way direct odd-sector proof data. -/
def NonnegativeOddBottom (D : DirectOddSufficientData.{u}) : Prop :=
  NonnegativeBottom D.oddBottom

/-- Nonnegativity of the supplied odd-sector bottom proves RH under one-way
direct odd-sector proof data. -/
theorem rh_of_nonnegativeOddBottom
    (D : DirectOddSufficientData.{u})
    (hodd : NonnegativeOddBottom D) :
    RiemannHypothesis :=
  D.riemannHypothesis_of_nonnegativeOddBottom hodd

/-- Odd-bottom nonnegativity restricted to a region of scales. -/
def OddBottomNonnegativeOn (D : DirectOddSufficientData.{u})
    (region : D.Scale → Prop) : Prop :=
  BottomNonnegativeOn D.oddBottom region

/-- A regional comparison from a full bottom to the direct odd-sector bottom. -/
def FullBottomLeOddOn (D : DirectOddSufficientData.{u})
    (fullBottom : D.Scale → ℝ) (region : D.Scale → Prop) : Prop :=
  BottomLeOn fullBottom D.oddBottom region

/-- A small-scale full-bottom positivity theorem can discharge the direct
odd-sector small row once the full-to-odd min-max comparison is supplied. -/
theorem oddBottomNonnegativeOn_of_fullBottom
    (D : DirectOddSufficientData.{u}) {fullBottom : D.Scale → ℝ}
    {region : D.Scale → Prop}
    (hfull : BottomNonnegativeOn fullBottom region)
    (hle : FullBottomLeOddOn D fullBottom region) :
    OddBottomNonnegativeOn D region :=
  bottomNonnegativeOn_of_leOn hfull hle

/-- Regional direct odd-bottom nonnegativity over a two-region cover assembles the
global odd-bottom row. -/
theorem nonnegativeOddBottom_of_scaleCover
    (D : DirectOddSufficientData.{u})
    (cover : ScaleCover D.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    NonnegativeOddBottom D :=
  nonnegativeBottom_of_scaleCover cover hSmall hLarge

/-- Under one-way direct odd-sector proof data, regional odd-bottom
nonnegativity over a small/large cover proves RH. -/
theorem rh_of_scaleCover
    (D : DirectOddSufficientData.{u})
    (cover : ScaleCover D.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    RiemannHypothesis :=
  rh_of_nonnegativeOddBottom D
    (nonnegativeOddBottom_of_scaleCover D cover hSmall hLarge)

end DirectOddSufficientData

/-- A packaged RH certificate for the one-way direct odd-sector route. -/
structure DirectOddSufficientCertificate where
  data : DirectOddSufficientData.{u}
  oddBottom_nonnegative : DirectOddSufficientData.NonnegativeOddBottom data

namespace DirectOddSufficientCertificate

/-- A packaged one-way direct odd-sector certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : DirectOddSufficientCertificate.{u}) :
    RiemannHypothesis :=
  DirectOddSufficientData.rh_of_nonnegativeOddBottom
    cert.data cert.oddBottom_nonnegative

end DirectOddSufficientCertificate

/-- A packaged regional RH certificate for the one-way direct odd-sector route.

For the Suzuki small-`a` handoff, the small row can be supplied from the
published small-scale positivity theorem plus a full-to-odd comparison, while
the large row remains the open tail. -/
structure DirectOddRegionalSufficientCertificate where
  data : DirectOddSufficientData.{u}
  cover : ScaleCover data.Scale
  oddSmall_nonnegative : DirectOddSufficientData.OddBottomNonnegativeOn data cover.small
  oddLarge_nonnegative : DirectOddSufficientData.OddBottomNonnegativeOn data cover.large

namespace DirectOddRegionalSufficientCertificate

/-- A packaged regional one-way direct odd-sector certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : DirectOddRegionalSufficientCertificate.{u}) :
    RiemannHypothesis :=
  DirectOddSufficientData.rh_of_scaleCover cert.data cert.cover
    cert.oddSmall_nonnegative cert.oddLarge_nonnegative

end DirectOddRegionalSufficientCertificate

/-- Direct Lean-facing proof data for the Yoshida/Suzuki odd-function route.

Supplying this structure for a concrete zeta Weil-form family is the analytic
two-way criterion.  The forward field is enough for an RH certificate; the
reverse field is only needed when using the iff or falsifier wrappers below.
This structure itself only records the interface and does not prove the
criterion. -/
structure DirectOddProofData where
  Scale : Type u
  oddBottom : Scale → ℝ
  riemannHypothesis_of_nonnegativeOddBottom :
    NonnegativeBottom oddBottom → RiemannHypothesis
  nonnegativeOddBottom_of_riemannHypothesis :
    RiemannHypothesis → NonnegativeBottom oddBottom

namespace DirectOddProofData

/-- Forget the converse row and keep only the one-way odd-sector sufficiency
data needed to prove RH. -/
def toSufficientData (D : DirectOddProofData.{u}) :
    DirectOddSufficientData.{u} where
  Scale := D.Scale
  oddBottom := D.oddBottom
  riemannHypothesis_of_nonnegativeOddBottom :=
    D.riemannHypothesis_of_nonnegativeOddBottom

/-- The remaining positivity row for direct odd-sector proof data. -/
def NonnegativeOddBottom (D : DirectOddProofData.{u}) : Prop :=
  NonnegativeBottom D.oddBottom

/-- Direct odd-sector proof data identifies RH with the supplied odd-bottom
nonnegativity row. -/
theorem riemannHypothesis_iff_nonnegativeOddBottom
    (D : DirectOddProofData.{u}) :
    RiemannHypothesis ↔ NonnegativeOddBottom D := by
  constructor
  · exact D.nonnegativeOddBottom_of_riemannHypothesis
  · exact D.riemannHypothesis_of_nonnegativeOddBottom

/-- Nonnegativity of the supplied odd-sector bottom proves RH under direct
odd-sector proof data. -/
theorem rh_of_nonnegativeOddBottom
    (D : DirectOddProofData.{u})
    (hodd : NonnegativeOddBottom D) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_nonnegativeOddBottom D).2 hodd

/-- RH gives the supplied odd-sector bottom row under direct odd-sector proof
data. -/
theorem nonnegativeOddBottom_of_rh
    (D : DirectOddProofData.{u})
    (hRH : RiemannHypothesis) :
    NonnegativeOddBottom D :=
  (riemannHypothesis_iff_nonnegativeOddBottom D).1 hRH

/-- Odd-bottom nonnegativity restricted to a region of scales. -/
def OddBottomNonnegativeOn (D : DirectOddProofData.{u})
    (region : D.Scale → Prop) : Prop :=
  BottomNonnegativeOn D.oddBottom region

/-- A regional comparison from a full bottom to the direct odd-sector bottom. -/
def FullBottomLeOddOn (D : DirectOddProofData.{u})
    (fullBottom : D.Scale → ℝ) (region : D.Scale → Prop) : Prop :=
  BottomLeOn fullBottom D.oddBottom region

/-- A small-scale full-bottom positivity theorem can discharge the direct
odd-sector small row once the full-to-odd min-max comparison is supplied. -/
theorem oddBottomNonnegativeOn_of_fullBottom
    (D : DirectOddProofData.{u}) {fullBottom : D.Scale → ℝ}
    {region : D.Scale → Prop}
    (hfull : BottomNonnegativeOn fullBottom region)
    (hle : FullBottomLeOddOn D fullBottom region) :
    OddBottomNonnegativeOn D region :=
  bottomNonnegativeOn_of_leOn hfull hle

/-- Regional direct odd-bottom nonnegativity over a two-region cover assembles the
global odd-bottom row. -/
theorem nonnegativeOddBottom_of_scaleCover
    (D : DirectOddProofData.{u})
    (cover : ScaleCover D.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    NonnegativeOddBottom D :=
  nonnegativeBottom_of_scaleCover cover hSmall hLarge

/-- Under direct odd-sector proof data, regional odd-bottom nonnegativity over a
small/large cover proves RH. -/
theorem rh_of_scaleCover
    (D : DirectOddProofData.{u})
    (cover : ScaleCover D.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    RiemannHypothesis :=
  rh_of_nonnegativeOddBottom D
    (nonnegativeOddBottom_of_scaleCover D cover hSmall hLarge)

end DirectOddProofData

/-- A packaged RH certificate for the direct odd-sector route. -/
structure DirectOddRHCertificate where
  data : DirectOddProofData.{u}
  oddBottom_nonnegative : DirectOddProofData.NonnegativeOddBottom data

namespace DirectOddRHCertificate

/-- A packaged direct odd-sector certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : DirectOddRHCertificate.{u}) :
    RiemannHypothesis :=
  DirectOddProofData.rh_of_nonnegativeOddBottom
    cert.data cert.oddBottom_nonnegative

end DirectOddRHCertificate

/-- A packaged regional RH certificate for the two-way direct odd-sector route. -/
structure DirectOddRegionalRHCertificate where
  data : DirectOddProofData.{u}
  cover : ScaleCover data.Scale
  oddSmall_nonnegative : DirectOddProofData.OddBottomNonnegativeOn data cover.small
  oddLarge_nonnegative : DirectOddProofData.OddBottomNonnegativeOn data cover.large

namespace DirectOddRegionalRHCertificate

/-- A packaged regional direct odd-sector certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : DirectOddRegionalRHCertificate.{u}) :
    RiemannHypothesis :=
  DirectOddProofData.rh_of_scaleCover cert.data cert.cover
    cert.oddSmall_nonnegative cert.oddLarge_nonnegative

end DirectOddRegionalRHCertificate

/-- A negative direct odd-sector bottom at one scale is a packaged falsifier
for the same supplied direct odd-sector proof data. -/
structure DirectOddFalsifier where
  data : DirectOddProofData.{u}
  scale : data.Scale
  oddBottom_lt_zero : data.oddBottom scale < 0

namespace DirectOddFalsifier

/-- A packaged negative direct odd-sector bottom refutes mathlib's
`RiemannHypothesis` under the supplied direct odd-sector proof data. -/
theorem not_riemannHypothesis
    (cert : DirectOddFalsifier.{u}) :
    ¬ RiemannHypothesis := by
  intro hRH
  have hnonneg :
      0 ≤ cert.data.oddBottom cert.scale :=
    cert.data.nonnegativeOddBottom_of_riemannHypothesis hRH cert.scale
  exact (not_le_of_gt cert.oddBottom_lt_zero) hnonneg

end DirectOddFalsifier

/-- The analytic/formal data needed before the odd-sector bottom row can be
consumed as an RH certificate through the stronger global-Morse/parity-split
route.  The field `evenProtected` is an open analytic input for a concrete zeta
Weil-form family. -/
structure ProofData where
  criterion : MorseIndexRHEquivalence.{u}
  parity : ParityMorseCalibration criterion
  oddCalibration :
    ParityMorseCalibration.OddLowestEigenvalueCalibration parity
  evenProtected : ParityMorseCalibration.EvenSectorProtected parity

/-- The remaining positivity row for packaged odd-sector proof data. -/
def NonnegativeOddBottom (D : ProofData.{u}) : Prop :=
  ParityMorseCalibration.NonnegativeOddBottom D.parity D.oddCalibration.oddBottom

/-- Packaged odd-sector proof data identifies RH with the single remaining
odd-bottom nonnegativity row. -/
theorem riemannHypothesis_iff_nonnegativeOddBottom
    (D : ProofData.{u}) :
    RiemannHypothesis ↔ NonnegativeOddBottom D := by
  exact
    ParityMorseCalibration.OddLowestEigenvalueCalibration.riemannHypothesis_iff_nonnegativeOddBottom_of_evenSectorProtected
      D.oddCalibration D.evenProtected

/-- The final odd-sector Morse proof handoff: once the data are supplied, global
nonnegativity of the calibrated odd-sector bottom proves RH. -/
theorem riemannHypothesis_of_nonnegativeOddBottom
    (D : ProofData.{u})
    (hodd : NonnegativeOddBottom D) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_nonnegativeOddBottom D).2 hodd

namespace ProofData

/-- The remaining odd-bottom row restricted to a region of scales. -/
def OddBottomNonnegativeOn (D : ProofData.{u})
    (region : D.criterion.Scale → Prop) : Prop :=
  BottomNonnegativeOn D.oddCalibration.oddBottom region

/-- A regional comparison from a full bottom to the calibrated odd-sector bottom. -/
def FullBottomLeOddOn (D : ProofData.{u})
    (fullBottom : D.criterion.Scale → ℝ)
    (region : D.criterion.Scale → Prop) : Prop :=
  BottomLeOn fullBottom D.oddCalibration.oddBottom region

/-- A small-scale full-bottom positivity theorem can discharge the calibrated
odd-sector small row once the full-to-odd min-max comparison is supplied. -/
theorem oddBottomNonnegativeOn_of_fullBottom
    (D : ProofData.{u}) {fullBottom : D.criterion.Scale → ℝ}
    {region : D.criterion.Scale → Prop}
    (hfull : BottomNonnegativeOn fullBottom region)
    (hle : FullBottomLeOddOn D fullBottom region) :
    OddBottomNonnegativeOn D region :=
  bottomNonnegativeOn_of_leOn hfull hle

/-- Regional calibrated odd-bottom nonnegativity over a two-region cover
assembles the global odd-bottom row. -/
theorem nonnegativeOddBottom_of_scaleCover
    (D : ProofData.{u})
    (cover : ScaleCover D.criterion.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    NonnegativeOddBottom D := by
  intro a
  rcases cover.cover a with hsmall | hlarge
  · exact hSmall a hsmall
  · exact hLarge a hlarge

/-- Under packaged odd-sector Morse proof data, regional odd-bottom
nonnegativity over a small/large cover proves RH. -/
theorem riemannHypothesis_of_scaleCover
    (D : ProofData.{u})
    (cover : ScaleCover D.criterion.Scale)
    (hSmall : OddBottomNonnegativeOn D cover.small)
    (hLarge : OddBottomNonnegativeOn D cover.large) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeOddBottom D
    (nonnegativeOddBottom_of_scaleCover D cover hSmall hLarge)

end ProofData

/-- A packaged RH certificate for the odd-sector Morse route.  The field
`oddBottom_nonnegative` is the load-bearing row; the other fields identify the
criterion and calibrations it belongs to. -/
structure RHCertificate where
  data : ProofData.{u}
  oddBottom_nonnegative : NonnegativeOddBottom data

namespace RHCertificate

/-- A packaged odd-sector Morse certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : RHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeOddBottom cert.data cert.oddBottom_nonnegative

end RHCertificate

/-- A packaged regional RH certificate for the packaged odd-sector Morse route.

The even-sector protection row is already part of `data`; this certificate only
splits the remaining odd-sector bottom row into small-scale and large-tail
pieces. -/
structure RegionalOddMorseCertificate where
  data : ProofData.{u}
  cover : ScaleCover data.criterion.Scale
  oddSmall_nonnegative : ProofData.OddBottomNonnegativeOn data cover.small
  oddLarge_nonnegative : ProofData.OddBottomNonnegativeOn data cover.large

namespace RegionalOddMorseCertificate

/-- A packaged regional odd-sector Morse certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : RegionalOddMorseCertificate.{u}) :
    RiemannHypothesis :=
  ProofData.riemannHypothesis_of_scaleCover cert.data cert.cover
    cert.oddSmall_nonnegative cert.oddLarge_nonnegative

end RegionalOddMorseCertificate

/-- A negative calibrated odd-sector bottom at one scale is a packaged falsifier
for the same odd-sector Morse data. -/
structure Falsifier where
  data : ProofData.{u}
  scale : data.criterion.Scale
  oddBottom_lt_zero : data.oddCalibration.oddBottom scale < 0

namespace Falsifier

/-- A packaged negative odd-bottom certificate refutes mathlib's
`RiemannHypothesis` under the supplied odd-sector Morse data. -/
theorem not_riemannHypothesis
    (cert : Falsifier.{u}) :
    ¬ RiemannHypothesis :=
  ParityMorseCalibration.OddLowestEigenvalueCalibration.not_riemannHypothesis_of_oddBottom_lt
    cert.data.oddCalibration cert.oddBottom_lt_zero

end Falsifier

/-- The fully calibrated parity-bottom data needed before the global
Morse/parity-split route can be consumed as an RH certificate.

Unlike `ProofData`, this structure does not hide the even-sector obligation as a
bare `EvenSectorProtected` side hypothesis.  It records both min-max
calibrations, so the final certificate must supply nonnegativity of both
sector bottoms. -/
structure ParityBottomProofData where
  criterion : MorseIndexRHEquivalence.{u}
  parity : ParityMorseCalibration criterion
  oddCalibration :
    ParityMorseCalibration.OddLowestEigenvalueCalibration parity
  evenCalibration :
    ParityMorseCalibration.EvenLowestEigenvalueCalibration parity

/-- The odd-sector positivity row for fully calibrated parity-bottom data. -/
def ParityBottomProofData.NonnegativeOddBottom
    (D : ParityBottomProofData.{u}) : Prop :=
  ParityMorseCalibration.NonnegativeOddBottom D.parity D.oddCalibration.oddBottom

/-- The even-sector positivity row for fully calibrated parity-bottom data. -/
def ParityBottomProofData.NonnegativeEvenBottom
    (D : ParityBottomProofData.{u}) : Prop :=
  ParityMorseCalibration.NonnegativeEvenBottom D.parity D.evenCalibration.evenBottom

/-- The two visible positivity rows for fully calibrated parity-bottom data. -/
def ParityBottomProofData.NonnegativeBottoms
    (D : ParityBottomProofData.{u}) : Prop :=
  D.NonnegativeOddBottom ∧ D.NonnegativeEvenBottom

namespace ParityBottomProofData

/-- Fully calibrated parity-bottom proof data identifies RH with nonnegativity
of both calibrated sector bottoms. -/
theorem riemannHypothesis_iff_nonnegativeBottoms
    (D : ParityBottomProofData.{u}) :
    RiemannHypothesis ↔ D.NonnegativeBottoms := by
  exact
    ParityMorseCalibration.OddLowestEigenvalueCalibration.riemannHypothesis_iff_nonnegativeOddBottom_and_nonnegativeEvenBottom
      D.oddCalibration D.evenCalibration

/-- Nonnegativity of both calibrated sector bottoms proves RH under fully
calibrated parity-bottom data. -/
theorem riemannHypothesis_of_nonnegativeBottoms
    (D : ParityBottomProofData.{u})
    (hbottoms : D.NonnegativeBottoms) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_nonnegativeBottoms D).2 hbottoms

/-- RH implies both calibrated sector bottoms are nonnegative under fully
calibrated parity-bottom data. -/
theorem nonnegativeBottoms_of_riemannHypothesis
    (D : ParityBottomProofData.{u})
    (hRH : RiemannHypothesis) :
    D.NonnegativeBottoms :=
  (riemannHypothesis_iff_nonnegativeBottoms D).1 hRH

end ParityBottomProofData

/-- A packaged RH certificate for the fully calibrated parity-bottom route.

Both bottom nonnegativity fields are load-bearing analytic rows for a concrete
zeta Weil-form family. -/
structure ParityBottomRHCertificate where
  data : ParityBottomProofData.{u}
  oddBottom_nonnegative : data.NonnegativeOddBottom
  evenBottom_nonnegative : data.NonnegativeEvenBottom

namespace ParityBottomRHCertificate

/-- A packaged fully calibrated parity-bottom certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : ParityBottomRHCertificate.{u}) :
    RiemannHypothesis :=
  ParityBottomProofData.riemannHypothesis_of_nonnegativeBottoms cert.data
    ⟨cert.oddBottom_nonnegative, cert.evenBottom_nonnegative⟩

end ParityBottomRHCertificate

/-- A negative calibrated odd-sector bottom at one scale is a packaged falsifier
for the fully calibrated parity-bottom data. -/
structure ParityBottomOddFalsifier where
  data : ParityBottomProofData.{u}
  scale : data.criterion.Scale
  oddBottom_lt_zero : data.oddCalibration.oddBottom scale < 0

namespace ParityBottomOddFalsifier

/-- A packaged negative odd-bottom certificate refutes mathlib's
`RiemannHypothesis` under fully calibrated parity-bottom data. -/
theorem not_riemannHypothesis
    (cert : ParityBottomOddFalsifier.{u}) :
    ¬ RiemannHypothesis :=
  ParityMorseCalibration.OddLowestEigenvalueCalibration.not_riemannHypothesis_of_oddBottom_lt
    cert.data.oddCalibration cert.oddBottom_lt_zero

end ParityBottomOddFalsifier

/-- A negative calibrated even-sector bottom at one scale is a packaged
falsifier for the fully calibrated parity-bottom data. -/
structure ParityBottomEvenFalsifier where
  data : ParityBottomProofData.{u}
  scale : data.criterion.Scale
  evenBottom_lt_zero : data.evenCalibration.evenBottom scale < 0

namespace ParityBottomEvenFalsifier

/-- A packaged negative even-bottom certificate refutes mathlib's
`RiemannHypothesis` under fully calibrated parity-bottom data. -/
theorem not_riemannHypothesis
    (cert : ParityBottomEvenFalsifier.{u}) :
    ¬ RiemannHypothesis :=
  ParityMorseCalibration.EvenLowestEigenvalueCalibration.not_riemannHypothesis_of_evenBottom_lt
    cert.data.evenCalibration cert.evenBottom_lt_zero

end ParityBottomEvenFalsifier

/-- A two-region cover of the scale parameter for a fully calibrated
parity-bottom certificate.

The intended use is the Suzuki/Yoshida split between a small-`a` regime and the
large-`a` tail.  The structure only records the cover; proving either regional
positivity row remains analytic input. -/
structure ScaleRegionCover (D : ParityBottomProofData.{u}) where
  small : D.criterion.Scale → Prop
  large : D.criterion.Scale → Prop
  cover : ∀ a : D.criterion.Scale, small a ∨ large a

namespace ScaleRegionCover

/-- The ordered cutoff cover `a ≤ cutoff` or `cutoff ≤ a`.

This is the Lean-facing shape for separating a small-scale theorem from a
large-tail theorem when the scale parameter is linearly ordered. -/
def ofCutoff (D : ParityBottomProofData.{u})
    [LinearOrder D.criterion.Scale]
    (cutoff : D.criterion.Scale) : ScaleRegionCover D where
  small a := a ≤ cutoff
  large a := cutoff ≤ a
  cover a := le_total a cutoff

end ScaleRegionCover

/-- Odd-sector bottom nonnegativity restricted to a region of scales. -/
def OddBottomNonnegativeOn (D : ParityBottomProofData.{u})
    (region : D.criterion.Scale → Prop) : Prop :=
  ∀ a : D.criterion.Scale, region a → 0 ≤ D.oddCalibration.oddBottom a

/-- Even-sector bottom nonnegativity restricted to a region of scales. -/
def EvenBottomNonnegativeOn (D : ParityBottomProofData.{u})
    (region : D.criterion.Scale → Prop) : Prop :=
  ∀ a : D.criterion.Scale, region a → 0 ≤ D.evenCalibration.evenBottom a

namespace ParityBottomProofData

/-- Regional nonnegativity over a two-region cover assembles the global
two-bottom row. -/
theorem nonnegativeBottoms_of_regionCover
    (D : ParityBottomProofData.{u})
    (cover : ScaleRegionCover D)
    (hOddSmall : OddBottomNonnegativeOn D cover.small)
    (hOddLarge : OddBottomNonnegativeOn D cover.large)
    (hEvenSmall : EvenBottomNonnegativeOn D cover.small)
    (hEvenLarge : EvenBottomNonnegativeOn D cover.large) :
    D.NonnegativeBottoms := by
  constructor
  · intro a
    rcases cover.cover a with hsmall | hlarge
    · exact hOddSmall a hsmall
    · exact hOddLarge a hlarge
  · intro a
    rcases cover.cover a with hsmall | hlarge
    · exact hEvenSmall a hsmall
    · exact hEvenLarge a hlarge

/-- Under fully calibrated parity-bottom data, regional nonnegativity over a
small/large cover proves RH.

This theorem is a handoff splitter only: it does not prove the small-scale
Suzuki row or the large-tail positivity row. -/
theorem riemannHypothesis_of_regionCover
    (D : ParityBottomProofData.{u})
    (cover : ScaleRegionCover D)
    (hOddSmall : OddBottomNonnegativeOn D cover.small)
    (hOddLarge : OddBottomNonnegativeOn D cover.large)
    (hEvenSmall : EvenBottomNonnegativeOn D cover.small)
    (hEvenLarge : EvenBottomNonnegativeOn D cover.large) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeBottoms D
    (nonnegativeBottoms_of_regionCover D cover
      hOddSmall hOddLarge hEvenSmall hEvenLarge)

end ParityBottomProofData

/-- The four bottom rows for an ordered cutoff split.

For a concrete Suzuki scale this is the place to feed the small-scale
archimedean theorem on `a ≤ cutoff` and the remaining large-tail theorem on
`cutoff ≤ a`. -/
structure CutoffParityBottomRows
    (D : ParityBottomProofData.{u}) [LinearOrder D.criterion.Scale]
    (cutoff : D.criterion.Scale) where
  oddSmall_nonnegative :
    ∀ a : D.criterion.Scale, a ≤ cutoff → 0 ≤ D.oddCalibration.oddBottom a
  oddLarge_nonnegative :
    ∀ a : D.criterion.Scale, cutoff ≤ a → 0 ≤ D.oddCalibration.oddBottom a
  evenSmall_nonnegative :
    ∀ a : D.criterion.Scale, a ≤ cutoff → 0 ≤ D.evenCalibration.evenBottom a
  evenLarge_nonnegative :
    ∀ a : D.criterion.Scale, cutoff ≤ a → 0 ≤ D.evenCalibration.evenBottom a

namespace ParityBottomProofData

/-- Cutoff-split odd/even bottom rows assemble the global two-bottom row. -/
theorem nonnegativeBottoms_of_cutoffRows
    (D : ParityBottomProofData.{u}) [LinearOrder D.criterion.Scale]
    (cutoff : D.criterion.Scale)
    (rows : CutoffParityBottomRows D cutoff) :
    D.NonnegativeBottoms :=
  nonnegativeBottoms_of_regionCover D (ScaleRegionCover.ofCutoff D cutoff)
    rows.oddSmall_nonnegative rows.oddLarge_nonnegative
    rows.evenSmall_nonnegative rows.evenLarge_nonnegative

/-- Under fully calibrated parity-bottom data, cutoff-split odd/even bottom
rows prove RH.

This theorem still assumes the large-tail rows.  It only exposes the common
small-scale / large-tail proof shape. -/
theorem riemannHypothesis_of_cutoffRows
    (D : ParityBottomProofData.{u}) [LinearOrder D.criterion.Scale]
    (cutoff : D.criterion.Scale)
    (rows : CutoffParityBottomRows D cutoff) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonnegativeBottoms D
    (nonnegativeBottoms_of_cutoffRows D cutoff rows)

end ParityBottomProofData

/-- A packaged RH certificate whose two parity-bottom rows are each supplied
regionally over a small/large scale cover.

For the zeta/Suzuki program, the small rows are expected to be archimedean and
the large rows contain the remaining per-place positivity problem.  This
structure keeps both pieces explicit. -/
structure RegionalParityBottomCertificate where
  data : ParityBottomProofData.{u}
  cover : ScaleRegionCover data
  oddSmall_nonnegative : OddBottomNonnegativeOn data cover.small
  oddLarge_nonnegative : OddBottomNonnegativeOn data cover.large
  evenSmall_nonnegative : EvenBottomNonnegativeOn data cover.small
  evenLarge_nonnegative : EvenBottomNonnegativeOn data cover.large

namespace RegionalParityBottomCertificate

/-- A packaged regional parity-bottom certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : RegionalParityBottomCertificate.{u}) :
    RiemannHypothesis :=
  ParityBottomProofData.riemannHypothesis_of_regionCover cert.data cert.cover
    cert.oddSmall_nonnegative cert.oddLarge_nonnegative
    cert.evenSmall_nonnegative cert.evenLarge_nonnegative

end RegionalParityBottomCertificate

end OddMorseCertificate
end JensenLadder
