import JensenLadder.SquaredDeterminantApproximation
import JensenLadder.SquaredDeterminantSpectralProduct
import JensenLadder.HurwitzRealRootedLimit
import JensenLadder.DerivativeBasepointConvergence

/-!
# Squared determinant Hurwitz bridge

This module connects the order-`1/2` squared determinant target to the proved
Hurwitz capstone.

If finite squared-variable determinants `D_a(w)` have all zeros on the
nonnegative real ray, then their pulled-back functions `z ↦ D_a(z^2)` have only
real zeros.  Therefore a locally-uniform limit of these pulled-back functions to
the pole-cancelled entire `Ξ` endpoint is enough to invoke
`HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire`.

The open burden is still explicit: construct the determinants, prove their
entireness after pullback, and prove locally-uniform convergence to `xiEntire`.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem
M does not prove RH by itself.
-/

namespace JensenLadder
namespace SquaredDeterminantHurwitzBridge

open Filter Topology

universe u

/-- Pull a squared-variable determinant `D(w)` back along `w = z^2`. -/
abbrev pulledBack
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (a : D.Scale) : ℂ → ℂ :=
  fun z => D.determinant a (z ^ 2)

/--
Zeros of the pulled-back determinant are real when squared determinant zeros lie
on the nonnegative real ray.
-/
theorem pulledBack_zero_real_of_allZerosNonnegativeReal
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (hnonneg : D.AllZerosNonnegativeReal) (a : D.Scale) {z : ℂ}
    (hz : pulledBack D a z = 0) :
    z.im = 0 := by
  rcases hnonneg a (z ^ 2) hz with ⟨E, hE, hz2⟩
  exact SquaredVariablePullback.im_eq_zero_of_sq_eq_nonneg_real hE hz2

/--
Squared-variable determinants feed the proved Hurwitz capstone after pullback.

This is the clean determinant target suggested by the evenness of `Ξ`: prove
that the order-`1/2` objects `D_a(w)` have nonnegative-real zeros, then prove
that `D_a(z^2)` converges locally uniformly to `xiEntire`.
-/
theorem riemannHypothesis_of_pulledBack_tendsto_xiEntire
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (pulledBack D (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hconv : TendstoLocallyUniformlyOn (fun n => pulledBack D (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis :=
  HurwitzBridge.riemannHypothesis_of_realRooted_tendsto_xiEntire
    (fun n => pulledBack D (scale n)) hFa
    (fun n _ hz => pulledBack_zero_real_of_allZerosNonnegativeReal
      D hnonneg (scale n) hz)
    hconv

/--
If RH is false, the same nonnegative-zero and analyticity rows refute the
claimed locally-uniform convergence to `xiEntire`.
-/
theorem not_pulledBack_tendsto_xiEntire_of_not_riemannHypothesis
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (pulledBack D (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal) (hnot : ¬ RiemannHypothesis) :
    ¬ TendstoLocallyUniformlyOn (fun n => pulledBack D (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ := by
  intro hconv
  exact hnot
    (riemannHypothesis_of_pulledBack_tendsto_xiEntire D scale hFa hnonneg hconv)

/-- Analyticity of `D_a(w)` implies analyticity after the pullback `w = z^2`. -/
theorem pulledBackAnalyticOnNhd_of_determinant_analytic
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (a : D.Scale)
    (hFa : AnalyticOnNhd ℂ (D.determinant a) Set.univ) :
    AnalyticOnNhd ℂ (pulledBack D a) Set.univ := by
  have hdiff : Differentiable ℂ (pulledBack D a) := by
    intro z
    unfold pulledBack
    exact (hFa (z ^ 2) (Set.mem_univ _)).differentiableAt.comp z
      (by fun_prop)
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

/-- Chain rule for the squared-variable pullback `z ↦ D_a(z^2)`. -/
theorem deriv_pulledBack_eq_chain
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (a : D.Scale)
    (hFa : AnalyticOnNhd ℂ (D.determinant a) Set.univ) (z : ℂ) :
    deriv (pulledBack D a) z =
      (2 * z) * deriv (D.determinant a) (z ^ 2) := by
  unfold pulledBack
  have houter :
      HasDerivAt (D.determinant a) (deriv (D.determinant a) (z ^ 2)) (z ^ 2) :=
    (hFa (z ^ 2) (Set.mem_univ _)).differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := by
    simpa [pow_two, two_mul] using ((hasDerivAt_id z).mul (hasDerivAt_id z))
  have hcomp : HasDerivAt (fun z : ℂ => D.determinant a (z ^ 2))
      (deriv (D.determinant a) (z ^ 2) * (2 * z)) z :=
    houter.comp z hinner
  rw [hcomp.deriv]
  ring

/--
Derivative/basepoint form of the squared determinant Hurwitz bridge.

Instead of supplying locally-uniform convergence of the pulled-back determinants
directly, it is enough to prove locally-uniform convergence of their derivatives
to `deriv xiEntire`, plus convergence at one basepoint.
-/
theorem riemannHypothesis_of_pulledBack_deriv_tendsto_xiEntire_at_basepoint
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale) (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (pulledBack D (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack D (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack D (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀))) :
    RiemannHypothesis := by
  have hFdiff : ∀ᶠ n in Filter.atTop,
      Differentiable ℂ (pulledBack D (scale n)) :=
    Filter.Eventually.of_forall fun n z =>
      (hFa n z (Set.mem_univ z)).differentiableAt
  have hconv : TendstoLocallyUniformlyOn (fun n => pulledBack D (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ :=
    DerivativeBasepointConvergence.tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ_basepoint
      (fun n => pulledBack D (scale n)) HurwitzBridge.xiEntire w₀
      hFdiff HurwitzBridge.xiEntire_differentiable hderiv hbase
  exact riemannHypothesis_of_pulledBack_tendsto_xiEntire D scale hFa hnonneg hconv

/-- Basepoint-`0` specialization of the derivative/basepoint squared bridge. -/
theorem riemannHypothesis_of_pulledBack_deriv_tendsto_xiEntire
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (pulledBack D (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack D (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack D (scale n) 0) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire 0))) :
    RiemannHypothesis :=
  riemannHypothesis_of_pulledBack_deriv_tendsto_xiEntire_at_basepoint
    D scale 0 hFa hnonneg hderiv hbase

/--
Chain-rule derivative/basepoint form of the squared determinant Hurwitz bridge.

This is the form closest to a trace formula in the squared variable `w`: prove
convergence of `2*z * d/dw D_a(w)` evaluated at `w = z^2`, plus one basepoint
normalization.
-/
theorem riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale) (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => (2 * z) * deriv (D.determinant (scale n)) (z ^ 2))
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack D (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀))) :
    RiemannHypothesis := by
  have hPull :
      ∀ n, AnalyticOnNhd ℂ (pulledBack D (scale n)) Set.univ :=
    fun n => pulledBackAnalyticOnNhd_of_determinant_analytic D (scale n) (hFa n)
  have hderivPull : TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack D (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ := by
    have hfun :
        (fun n z => deriv (pulledBack D (scale n)) z) =
          fun n z => (2 * z) * deriv (D.determinant (scale n)) (z ^ 2) := by
      funext n z
      exact deriv_pulledBack_eq_chain D (scale n) (hFa n) z
    simpa [hfun] using hderiv
  exact riemannHypothesis_of_pulledBack_deriv_tendsto_xiEntire_at_basepoint
    D scale w₀ hPull hnonneg hderivPull hbase

/-- Basepoint-`0` specialization of the chain-rule squared bridge. -/
theorem riemannHypothesis_of_chainDeriv_tendsto_xiEntire
    (D : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hnonneg : D.AllZerosNonnegativeReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => (2 * z) * deriv (D.determinant (scale n)) (z ^ 2))
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack D (scale n) 0) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire 0))) :
    RiemannHypothesis :=
  riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    D scale 0 hFa hnonneg hderiv hbase

/-- Packaged certificate for the squared-determinant Hurwitz route. -/
structure Certificate where
  approximants : SquaredDeterminantApproximation.SquaredDeterminantApproximants.{u}
  scale : ℕ → approximants.Scale
  allZerosNonnegativeReal : approximants.AllZerosNonnegativeReal
  pulledBackAnalyticOnNhd :
    ∀ n, AnalyticOnNhd ℂ (pulledBack approximants (scale n)) Set.univ
  pulledBackTendstoXiEntire :
    TendstoLocallyUniformlyOn (fun n => pulledBack approximants (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ

namespace Certificate

/-- A packaged squared-determinant Hurwitz certificate proves mathlib's RH. -/
theorem riemannHypothesis (cert : Certificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_pulledBack_tendsto_xiEntire cert.approximants cert.scale
    cert.pulledBackAnalyticOnNhd cert.allZerosNonnegativeReal
    cert.pulledBackTendstoXiEntire

end Certificate

namespace FiniteSpectralProduct

open scoped BigOperators

/-- Finite squared spectral products are entire in the squared variable `w`. -/
theorem determinantAnalyticOnNhd
    (S : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.{u}) :
    AnalyticOnNhd ℂ S.determinant Set.univ := by
  classical
  letI := S.fintype
  have hd :
      Differentiable ℂ (fun w : ℂ => ∏ i : S.Index, ((S.energy i : ℂ) - w)) := by
    fun_prop
  simpa [SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.determinant] using
    hd.differentiableOn.analyticOnNhd isOpen_univ

/-- A finite spectral-product family supplies determinant analyticity in `w`. -/
theorem familyDeterminantAnalyticOnNhd
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u}) :
    ∀ a, AnalyticOnNhd ℂ (F.approximants.determinant a) Set.univ := by
  intro a
  simpa [SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.approximants] using
    determinantAnalyticOnNhd (F.spectrum a)

/--
Finite squared spectral products are entire after the pullback `w = z^2`.

This discharges the mechanical analyticity row for the finite-product case; the
load-bearing row remains locally-uniform convergence to `xiEntire`.
-/
theorem pulledBackAnalyticOnNhd
    (S : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.{u}) :
    AnalyticOnNhd ℂ (fun z : ℂ => S.determinant (z ^ 2)) Set.univ := by
  classical
  letI := S.fintype
  have hd :
      Differentiable ℂ
        (fun z : ℂ => ∏ i : S.Index, ((S.energy i : ℂ) - z ^ 2)) := by
    fun_prop
  simpa [SquaredDeterminantSpectralProduct.FiniteSquaredSpectrum.determinant] using
    hd.differentiableOn.analyticOnNhd isOpen_univ

/-- A finite spectral-product family supplies the pulled-back analyticity row. -/
theorem familyPulledBackAnalyticOnNhd
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale) :
    ∀ n, AnalyticOnNhd ℂ (pulledBack F.approximants (scale n)) Set.univ := by
  intro n
  simpa [pulledBack,
    SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.approximants] using
    pulledBackAnalyticOnNhd (F.spectrum (scale n))

/--
Finite nonnegative squared spectral products feed the Hurwitz capstone once
their pulled-back determinants converge locally uniformly to `xiEntire`.
-/
theorem riemannHypothesis_of_tendsto_xiEntire
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale)
    (hconv : TendstoLocallyUniformlyOn (fun n => pulledBack F.approximants (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis :=
  riemannHypothesis_of_pulledBack_tendsto_xiEntire F.approximants scale
    (familyPulledBackAnalyticOnNhd F scale)
    F.allZerosNonnegativeReal hconv

/--
For finite nonnegative squared spectral products, a false RH refutes the
locally-uniform convergence row to `xiEntire`.
-/
theorem not_tendsto_xiEntire_of_not_riemannHypothesis
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale)
    (hnot : ¬ RiemannHypothesis) :
    ¬ TendstoLocallyUniformlyOn (fun n => pulledBack F.approximants (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ :=
  not_pulledBack_tendsto_xiEntire_of_not_riemannHypothesis F.approximants scale
    (familyPulledBackAnalyticOnNhd F scale)
    F.allZerosNonnegativeReal hnot

/--
Derivative/basepoint form for finite nonnegative squared spectral products.

The finite-product zero location and analyticity rows are automatic; the
remaining input is derivative convergence plus one basepoint normalization.
-/
theorem riemannHypothesis_of_deriv_tendsto_xiEntire_at_basepoint
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale) (w₀ : ℂ)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack F.approximants (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack F.approximants (scale n) w₀)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire w₀))) :
    RiemannHypothesis :=
  riemannHypothesis_of_pulledBack_deriv_tendsto_xiEntire_at_basepoint
    F.approximants scale w₀
    (familyPulledBackAnalyticOnNhd F scale)
    F.allZerosNonnegativeReal hderiv hbase

/-- Basepoint-`0` finite spectral-product derivative/basepoint specialization. -/
theorem riemannHypothesis_of_deriv_tendsto_xiEntire
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack F.approximants (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack F.approximants (scale n) 0)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire 0))) :
    RiemannHypothesis :=
  riemannHypothesis_of_deriv_tendsto_xiEntire_at_basepoint
    F scale 0 hderiv hbase

/--
Chain-rule derivative/basepoint form for finite nonnegative squared spectral
products.  The remaining input is convergence of the squared-variable
chain-rule derivative plus one basepoint normalization.
-/
theorem riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale) (w₀ : ℂ)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => (2 * z) * deriv (F.approximants.determinant (scale n)) (z ^ 2))
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack F.approximants (scale n) w₀)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire w₀))) :
    RiemannHypothesis :=
  JensenLadder.SquaredDeterminantHurwitzBridge.riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    F.approximants scale w₀
    (fun n => familyDeterminantAnalyticOnNhd F (scale n))
    F.allZerosNonnegativeReal hderiv hbase

/-- Basepoint-`0` finite spectral-product chain-rule specialization. -/
theorem riemannHypothesis_of_chainDeriv_tendsto_xiEntire
    (F : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u})
    (scale : ℕ → F.Scale)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => (2 * z) * deriv (F.approximants.determinant (scale n)) (z ^ 2))
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => pulledBack F.approximants (scale n) 0)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire 0))) :
    RiemannHypothesis :=
  riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    F scale 0 hderiv hbase

/-- Packaged finite spectral-product Hurwitz certificate. -/
structure Certificate where
  family : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u}
  scale : ℕ → family.Scale
  pulledBackTendstoXiEntire :
    TendstoLocallyUniformlyOn (fun n => pulledBack family.approximants (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ

namespace Certificate

/-- A packaged finite spectral-product Hurwitz certificate proves mathlib's RH. -/
theorem riemannHypothesis (cert : Certificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_tendsto_xiEntire cert.family cert.scale
    cert.pulledBackTendstoXiEntire

end Certificate

/-- Packaged finite spectral-product derivative/basepoint certificate. -/
structure DerivativeBasepointCertificate where
  family : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u}
  scale : ℕ → family.Scale
  basepoint : ℂ
  pulledBackDerivTendstoXiEntire :
    TendstoLocallyUniformlyOn
      (fun n z => deriv (pulledBack family.approximants (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ
  pulledBackBasepointTendstoXiEntire :
    Tendsto (fun n => pulledBack family.approximants (scale n) basepoint)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire basepoint))

namespace DerivativeBasepointCertificate

/--
A packaged finite spectral-product derivative/basepoint certificate proves
mathlib's RH.
-/
theorem riemannHypothesis (cert : DerivativeBasepointCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_deriv_tendsto_xiEntire_at_basepoint
    cert.family cert.scale cert.basepoint
    cert.pulledBackDerivTendstoXiEntire
    cert.pulledBackBasepointTendstoXiEntire

end DerivativeBasepointCertificate

/-- Packaged finite spectral-product chain-rule derivative/basepoint certificate. -/
structure ChainDerivativeBasepointCertificate where
  family : SquaredDeterminantSpectralProduct.FiniteSquaredSpectrumFamily.{u}
  scale : ℕ → family.Scale
  basepoint : ℂ
  chainDerivTendstoXiEntire :
    TendstoLocallyUniformlyOn
      (fun n z =>
        (2 * z) * deriv (family.approximants.determinant (scale n)) (z ^ 2))
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ
  pulledBackBasepointTendstoXiEntire :
    Tendsto (fun n => pulledBack family.approximants (scale n) basepoint)
      Filter.atTop (𝓝 (HurwitzBridge.xiEntire basepoint))

namespace ChainDerivativeBasepointCertificate

/--
A packaged finite spectral-product chain-rule derivative/basepoint certificate
proves mathlib's RH.
-/
theorem riemannHypothesis (cert : ChainDerivativeBasepointCertificate.{u}) :
    RiemannHypothesis :=
  riemannHypothesis_of_chainDeriv_tendsto_xiEntire_at_basepoint
    cert.family cert.scale cert.basepoint
    cert.chainDerivTendstoXiEntire
    cert.pulledBackBasepointTendstoXiEntire

end ChainDerivativeBasepointCertificate

end FiniteSpectralProduct

end SquaredDeterminantHurwitzBridge
end JensenLadder
