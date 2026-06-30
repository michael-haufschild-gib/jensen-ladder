import GaloisForLFunctions.Core

/-!
# Consolidated bridge implications

This file formalizes implication skeletons extracted from
`docs/consolidated/03-theorems-toward-rh.md`,
`docs/consolidated/07-theorems-and-lemmas-required.md`, and
`docs/consolidated/08-conjectures-required.md`.

The analytic/native hypotheses themselves are not proved here.  The point is to
make the promised conclusions machine-checkable once the missing hypotheses are
supplied:

* the two-lemma transport bridge forces all zeros onto the seam;
* a support/measure confinement bridge forces the same conclusion;
* an RH-false iff bridge plus confinement forces the same conclusion;
* a finite faithful index equal to the off-line count, if forced to vanish,
  gives a finite RH-like statement;
* a signed carrier with opposite signs separates the true object from a
  surrogate.

No RH proof, no Schanuel/DSS proof, and no source-built carrier construction is
asserted.
-/

namespace GaloisForLFunctions

noncomputable section

section TransportBridge

variable {Zero Defect : Type*}

/-- Abstract RH-like conclusion: every zero lies on the designated line. -/
def allZerosOnLine (OnLine : Zero → Prop) : Prop :=
  ∀ ρ, OnLine ρ

/-- Abstract defect confinement: every source-carrying defect lies on the seam. -/
def allSourceDefectsOnSeam (OnSeam SourceCarrying : Defect → Prop) : Prop :=
  ∀ d, SourceCarrying d → OnSeam d

/-- Abstract detection hypothesis: every off-line zero creates a source-carrying off-seam defect. -/
def detectsOffSeamDefect
    (OnLine : Zero → Prop) (OnSeam SourceCarrying : Defect → Prop) : Prop :=
  ∀ ρ, ¬ OnLine ρ → ∃ d, SourceCarrying d ∧ ¬ OnSeam d

/-- The consolidated two-lemma bridge, as pure logic:
if off-line zeros are detected by source-carrying off-seam defects, and all such
defects are confined to the seam, then every zero is on line. -/
theorem twoLemmaBridge_forces_onLine
    {OnLine : Zero → Prop} {OnSeam SourceCarrying : Defect → Prop}
    (hDetect : detectsOffSeamDefect OnLine OnSeam SourceCarrying)
    (hConfine : allSourceDefectsOnSeam OnSeam SourceCarrying) :
    allZerosOnLine OnLine := by
  intro ρ
  by_contra hOff
  rcases hDetect ρ hOff with ⟨d, hSource, hOffSeam⟩
  exact hOffSeam (hConfine d hSource)

/-- A linked off-seam source-carrying defect associated to a zero. -/
def offSeamSourceDefectFor
    (Link : Zero → Defect → Prop) (OnSeam SourceCarrying : Defect → Prop)
    (ρ : Zero) : Prop :=
  ∃ d, SourceCarrying d ∧ Link ρ d ∧ ¬ OnSeam d

/-- The RH-false bridge form from the consolidation:
if an off-line zero is equivalent to an off-seam source-carrying defect, then
seam confinement rules out off-line zeros. -/
theorem rhFalseBridge_forces_onLine
    {OnLine : Zero → Prop} {OnSeam SourceCarrying : Defect → Prop}
    {Link : Zero → Defect → Prop}
    (hIff : ∀ ρ, ¬ OnLine ρ ↔ offSeamSourceDefectFor Link OnSeam SourceCarrying ρ)
    (hConfine : allSourceDefectsOnSeam OnSeam SourceCarrying) :
    allZerosOnLine OnLine := by
  intro ρ
  by_contra hOff
  rcases (hIff ρ).mp hOff with ⟨d, hSource, _hLink, hOffSeam⟩
  exact hOffSeam (hConfine d hSource)

end TransportBridge

section SupportBridge

variable {Zero SupportPoint : Type*}

/-- Support confinement: every support point of the proposed source measure lies on the seam. -/
def supportConfinedToSeam
    (InSupport OnSeamSupport : SupportPoint → Prop) : Prop :=
  ∀ x, InSupport x → OnSeamSupport x

/-- Detection by support: an off-line zero produces an off-seam support point. -/
def offLineProducesOffSeamSupport
    (OnLine : Zero → Prop) (InSupport OnSeamSupport : SupportPoint → Prop) : Prop :=
  ∀ ρ, ¬ OnLine ρ → ∃ x, InSupport x ∧ ¬ OnSeamSupport x

/-- The source-measure bridge in abstract form:
support confined to the seam plus off-line-to-off-seam support detection forces
the RH-like conclusion. -/
theorem supportBridge_forces_onLine
    {OnLine : Zero → Prop} {InSupport OnSeamSupport : SupportPoint → Prop}
    (hDetect : offLineProducesOffSeamSupport OnLine InSupport OnSeamSupport)
    (hConfine : supportConfinedToSeam InSupport OnSeamSupport) :
    allZerosOnLine OnLine := by
  intro ρ
  by_contra hOff
  rcases hDetect ρ hOff with ⟨x, hxSupport, hxOffSeam⟩
  exact hxOffSeam (hConfine x hxSupport)

end SupportBridge

section FaithfulIndex

variable {Zero : Type*} [DecidableEq Zero]
variable (OffLine : Zero → Prop) [DecidablePred OffLine]

/-- Finite RH-like conclusion: no member of the finite carrier spectrum is off-line. -/
def finiteRHLike (zeros : Finset Zero) : Prop :=
  ∀ ρ ∈ zeros, ¬ OffLine ρ

/-- The finite off-line count used by the faithful-index skeleton. -/
def finiteOffLineCount (zeros : Finset Zero) : ℕ :=
  (zeros.filter OffLine).card

/-- A finite set has no off-line elements exactly when its off-line count is zero. -/
theorem finiteRHLike_iff_offLineCount_eq_zero (zeros : Finset Zero) :
    finiteRHLike OffLine zeros ↔ finiteOffLineCount OffLine zeros = 0 := by
  constructor
  · intro hNoOff
    rw [finiteOffLineCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
    intro ρ hρ
    exact hNoOff ρ (Finset.mem_of_mem_filter ρ hρ) (Finset.mem_filter.mp hρ).2
  · intro hCount ρ hρ hOff
    have hmem : ρ ∈ zeros.filter OffLine := Finset.mem_filter.mpr ⟨hρ, hOff⟩
    have hpos : 0 < (zeros.filter OffLine).card :=
      Finset.card_pos.mpr ⟨ρ, hmem⟩
    rw [finiteOffLineCount] at hCount
    omega

/-- The finite faithful-index route:
if the faithful index is exactly the off-line count, and the source construction
forces that index to vanish, then the finite carrier satisfies the RH-like
no-off-line conclusion. -/
theorem faithfulIndex_zero_forces_finiteRHLike
    {zeros : Finset Zero} {kappa : ℕ}
    (hFaithful : kappa = finiteOffLineCount OffLine zeros)
    (hVanish : kappa = 0) :
    finiteRHLike OffLine zeros := by
  rw [finiteRHLike_iff_offLineCount_eq_zero]
  rw [← hFaithful, hVanish]

end FaithfulIndex

section SignedCarrier

variable {Obj : Type*} (CarrierIntegral : Obj → ℝ)

/-- Opposite signed carrier integrals separate two objects.  This is the finite
logic behind the surrogate-ladder kill criterion for an oriented 2-form carrier:
if the true object is positive and a surrogate is negative for the same signed
functional, they cannot be the same object. -/
theorem signedCarrier_separates
    {trueObj surrogate : Obj}
    (hTrue : 0 < CarrierIntegral trueObj)
    (hSurrogate : CarrierIntegral surrogate < 0) :
    trueObj ≠ surrogate := by
  intro hEq
  subst surrogate
  linarith

/-- A signed carrier cannot both be strictly positive and strictly negative on
the same object. -/
theorem signedCarrier_not_both_signs
    {obj : Obj}
    (hPos : 0 < CarrierIntegral obj) :
    ¬ CarrierIntegral obj < 0 := by
  intro hNeg
  linarith

end SignedCarrier

end

end GaloisForLFunctions
