import JensenLadder.CVSSpectralRoute
import JensenLadder.SpectralRealization

/-!
# Pollution-free spectral limit handoff

This module names the extra obligations hidden inside a phrase such as
"finite spectra converge to the `Xi` zeros".

For a finite-approximation or truncation program, it is not enough that some
finite eigenvalues shadow some known zeros.  A proof of the spectral endpoint
must also say:

* tracked branches do not escape the limiting regime;
* persistent limiting branches are not spurious;
* every regular `Xi` zero is hit by a limiting branch.

Those three rows assemble to the existing exact regular spectral-realization
endpoint.  This file does not prove any analytic convergence theorem, exclusion
radius, rate, compactness result, or RH.  It only records the Lean-facing
handoff for a pollution-free approximation limit.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace SpectralPollutionFreeLimit

open CVSSpectralRoute
open SpectralRealization

universe u

/--
A branch-limit skeleton for a spectral approximation scheme.

`Branch` indexes the tracked spectral branches of the approximation.  The
predicate `branchHasLimit` and the value `limitHeight` are abstract analytic
inputs: a real proof must construct them from a concrete topology/norm/filter.
-/
structure CandidateLimit where
  Branch : Type u
  limitHeight : Branch -> ℝ
  branchHasLimit : Branch -> Prop

namespace CandidateLimit

/-- No tracked branch escapes the limiting regime. -/
def NoEscape (F : CandidateLimit.{u}) : Prop :=
  ∀ b : F.Branch, F.branchHasLimit b

/-- Every convergent limiting branch lands on a regular `Xi` zero. -/
def NoSpuriousLimit (F : CandidateLimit.{u}) : Prop :=
  ∀ b : F.Branch, F.branchHasLimit b ->
    RHReduction.riemannXiRegularZero (F.limitHeight b : ℂ)

/-- Every regular `Xi` zero is hit by some convergent limiting branch. -/
def LimitComplete (F : CandidateLimit.{u}) : Prop :=
  ∀ z : ℂ, RHReduction.riemannXiRegularZero z ->
    ∃ b : F.Branch, F.branchHasLimit b ∧ z = (F.limitHeight b : ℂ)

/-- The three rows needed for a pollution-free spectral approximation limit. -/
def PollutionFree (F : CandidateLimit.{u}) : Prop :=
  F.NoEscape ∧ F.NoSpuriousLimit ∧ F.LimitComplete

/-- A tracked branch with no limit blocks the no-escape row. -/
def EscapingBranch (F : CandidateLimit.{u}) : Prop :=
  ∃ b : F.Branch, ¬ F.branchHasLimit b

/-- A convergent limiting branch that is not a regular `Xi` zero. -/
def SpuriousLimit (F : CandidateLimit.{u}) : Prop :=
  ∃ b : F.Branch, F.branchHasLimit b ∧
    ¬ RHReduction.riemannXiRegularZero (F.limitHeight b : ℂ)

/-- A regular `Xi` zero missed by every convergent limiting branch. -/
def MissingRegularXiZero (F : CandidateLimit.{u}) : Prop :=
  ∃ z : ℂ, RHReduction.riemannXiRegularZero z ∧
    ∀ b : F.Branch, F.branchHasLimit b -> z ≠ (F.limitHeight b : ℂ)

/-- The three pollution-free rows assemble the existing exact regular spectral
realization endpoint. -/
def regularSpectralRealization_of_rows
    (F : CandidateLimit.{u})
    (hNoEscape : F.NoEscape)
    (hNoSpurious : F.NoSpuriousLimit)
    (hComplete : F.LimitComplete) :
    RiemannXiRegularSpectralRealization.{u} where
  Spectrum := F.Branch
  height := F.limitHeight
  sound := by
    intro b
    exact hNoSpurious b (hNoEscape b)
  complete := by
    intro z hz
    rcases hComplete z hz with ⟨b, _hb, hbz⟩
    exact ⟨b, hbz⟩

/-- A pollution-free limit supplies the existing exact regular spectral endpoint. -/
def regularSpectralRealization_of_pollutionFree
    (F : CandidateLimit.{u})
    (h : F.PollutionFree) :
    RiemannXiRegularSpectralRealization.{u} :=
  regularSpectralRealization_of_rows F h.1 h.2.1 h.2.2

/-- A pollution-free spectral approximation limit would prove mathlib's
`RiemannHypothesis`.

This is a reduction theorem.  The hard input is the pollution-free convergence
package, especially the no-spurious and completeness rows. -/
theorem riemannHypothesis_of_rows
    (F : CandidateLimit.{u})
    (hNoEscape : F.NoEscape)
    (hNoSpurious : F.NoSpuriousLimit)
    (hComplete : F.LimitComplete) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_rows F hNoEscape hNoSpurious hComplete)

/-- A pollution-free spectral approximation limit would prove mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_pollutionFree
    (F : CandidateLimit.{u})
    (h : F.PollutionFree) :
    RiemannHypothesis :=
  riemannHypothesis_of_regularSpectralRealization
    (regularSpectralRealization_of_pollutionFree F h)

/-- An escaping branch refutes the no-escape row. -/
theorem not_noEscape_of_escapingBranch
    (F : CandidateLimit.{u})
    (hesc : F.EscapingBranch) :
    ¬ F.NoEscape := by
  rintro hNoEscape
  rcases hesc with ⟨b, hb⟩
  exact hb (hNoEscape b)

/-- A spurious limiting branch refutes the no-spurious row. -/
theorem not_noSpuriousLimit_of_spuriousLimit
    (F : CandidateLimit.{u})
    (hspur : F.SpuriousLimit) :
    ¬ F.NoSpuriousLimit := by
  rintro hNoSpurious
  rcases hspur with ⟨b, hbLimit, hbNotZero⟩
  exact hbNotZero (hNoSpurious b hbLimit)

/-- A missed regular zero refutes the completeness row. -/
theorem not_limitComplete_of_missingRegularXiZero
    (F : CandidateLimit.{u})
    (hmiss : F.MissingRegularXiZero) :
    ¬ F.LimitComplete := by
  intro hComplete
  rcases hmiss with ⟨z, hz, hmissing⟩
  rcases hComplete z hz with ⟨b, hbLimit, hbz⟩
  exact hmissing b hbLimit hbz

/-- A missed regular zero blocks the full pollution-free package. -/
theorem not_pollutionFree_of_missingRegularXiZero
    (F : CandidateLimit.{u})
    (hmiss : F.MissingRegularXiZero) :
    ¬ F.PollutionFree := by
  intro h
  exact not_limitComplete_of_missingRegularXiZero F hmiss h.2.2

/-- A spurious limiting branch blocks the full pollution-free package. -/
theorem not_pollutionFree_of_spuriousLimit
    (F : CandidateLimit.{u})
    (hspur : F.SpuriousLimit) :
    ¬ F.PollutionFree := by
  intro h
  exact not_noSpuriousLimit_of_spuriousLimit F hspur h.2.1

/-- An escaping branch blocks the full pollution-free package. -/
theorem not_pollutionFree_of_escapingBranch
    (F : CandidateLimit.{u})
    (hesc : F.EscapingBranch) :
    ¬ F.PollutionFree := by
  intro h
  exact not_noEscape_of_escapingBranch F hesc h.1

/-- A non-real regular `Xi` zero is missed by every real-height limiting branch. -/
theorem missingRegularXiZero_of_nonrealRegularXiZero
    (F : CandidateLimit.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    F.MissingRegularXiZero := by
  refine ⟨z, hz, ?_⟩
  intro b _hbLimit hbz
  exact hzim (by
    rw [hbz]
    simp)

/-- A non-real regular `Xi` zero refutes the completeness row for any real-height
branch limit. -/
theorem not_limitComplete_of_nonrealRegularXiZero
    (F : CandidateLimit.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ F.LimitComplete :=
  not_limitComplete_of_missingRegularXiZero F
    (missingRegularXiZero_of_nonrealRegularXiZero F hz hzim)

/-- A non-real regular `Xi` zero blocks any pollution-free real-height limit. -/
theorem not_pollutionFree_of_nonrealRegularXiZero
    (F : CandidateLimit.{u}) {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ F.PollutionFree :=
  not_pollutionFree_of_missingRegularXiZero F
    (missingRegularXiZero_of_nonrealRegularXiZero F hz hzim)

/--
Package a pollution-free branch-limit theorem as the abstract C-vS
Hurwitz/convergence row.

The finite real-rooted approximants remain part of the C-vS architecture, but
the actual limiting content is the `PollutionFree` row supplied here.
-/
def hurwitzXiConvergenceOfPollutionFreeLimit
    (A : FiniteScaleApproximants.{u})
    (F : CandidateLimit.{u}) :
    HurwitzXiConvergence A where
  convergesToXi := F.PollutionFree
  regularXiZerosReal_of_approximantsReal_and_convergence := by
    intro _hreal h z hz
    exact regular_xi_zeros_real_of_regularSpectralRealization
      (regularSpectralRealization_of_pollutionFree F h) z hz

end CandidateLimit

/--
Packaged C-vS certificate whose convergence row has been refined into the
pollution-free branch-limit rows.

The finite simple-even row gives real zeros for finite approximants.  The
`pollutionFree` field is the load-bearing limiting theorem.
-/
structure PollutionFreeCVSRHCertificate where
  approximants : FiniteScaleApproximants.{u}
  groundStateData : SimpleEvenGroundStateData approximants
  limitData : CandidateLimit.{u}
  simpleEvenGroundStates : SimpleEvenGroundStates groundStateData
  pollutionFree : limitData.PollutionFree

namespace PollutionFreeCVSRHCertificate

/-- The refined pollution-free limit package supplies the C-vS convergence row. -/
def convergence
    (cert : PollutionFreeCVSRHCertificate.{u}) :
    HurwitzXiConvergence cert.approximants :=
  cert.limitData.hurwitzXiConvergenceOfPollutionFreeLimit cert.approximants

/-- A packaged pollution-free C-vS certificate proves mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis
    (cert : PollutionFreeCVSRHCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_simpleEvenGroundStates_and_convergence
    cert.groundStateData cert.convergence
    cert.simpleEvenGroundStates cert.pollutionFree

end PollutionFreeCVSRHCertificate

end SpectralPollutionFreeLimit
end JensenLadder
