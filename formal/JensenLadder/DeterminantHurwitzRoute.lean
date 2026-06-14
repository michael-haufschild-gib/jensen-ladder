import JensenLadder.CVSSpectralRoute
import JensenLadder.DerivativeBasepointConvergence
import JensenLadder.HurwitzRealRootedLimit

open scoped Topology

/-!
# Determinant Hurwitz route

This module specializes the abstract C-vS Hurwitz handoff to the determinant
route suggested by the CCM/Suzuki spectral-triple program.

The determinant route has a narrower shape than eigenvalue-branch tracking:

* each finite regularized determinant has only real zeros;
* the normalized determinants converge locally uniformly to `Xi`;
* Hurwitz/LP-closure transfers real-zero-ness to the regular `Xi` endpoint.

The analytic Hurwitz theorem and the local-uniform convergence estimate are not
proved here.  They are represented by the single load-bearing row
`locallyUniformToXi`, plus the transfer field that turns that row into reality of
regular `Xi` zeros.  This file only packages that row into the existing
`CVSSpectralRoute` interface.

Evidence class: formal/certificate artifact.  Theorem M is proven, but Theorem M
does not prove RH by itself.
-/

namespace JensenLadder
namespace DeterminantHurwitzRoute

open CVSSpectralRoute
open Filter

universe u

/--
A finite-scale family of regularized determinants.

For the intended CCM/Suzuki application, each `determinant a` is the normalized
regularized characteristic determinant of a finite self-adjoint operator.  This
structure deliberately stores only the function family needed by the zero-set
handoff; self-adjointness and regularization conventions are external analytic
data.
-/
structure DeterminantApproximants where
  Scale : Type u
  determinant : Scale -> Complex -> Complex

namespace DeterminantApproximants

/-- Forget determinant vocabulary and view the family as finite approximants. -/
def toFiniteScaleApproximants (D : DeterminantApproximants.{u}) :
    FiniteScaleApproximants.{u} where
  Scale := D.Scale
  approximant := D.determinant

/-- Every zero of every finite determinant is real. -/
def AllZerosReal (D : DeterminantApproximants.{u}) : Prop :=
  forall a : D.Scale, forall z : Complex, D.determinant a z = 0 -> z.im = 0

/-- Determinant real-zero data supplies the generic finite-approximant row. -/
theorem allApproximantZerosReal_of_allZerosReal
    (D : DeterminantApproximants.{u})
    (hreal : D.AllZerosReal) :
    AllApproximantZerosReal D.toFiniteScaleApproximants := by
  intro a z hz
  exact hreal a z hz

/-- The generic finite-approximant real-zero row is the same determinant row. -/
theorem allZerosReal_of_allApproximantZerosReal
    (D : DeterminantApproximants.{u})
    (hreal : AllApproximantZerosReal D.toFiniteScaleApproximants) :
    D.AllZerosReal := by
  intro a z hz
  exact hreal a z hz

/-- The pole-cancelled entire endpoint is analytic on all of `ℂ`. -/
theorem xiEntire_analyticOnNhd_univ :
    AnalyticOnNhd ℂ HurwitzBridge.xiEntire Set.univ := by
  exact (HurwitzBridge.xiEntire_differentiable.differentiableOn).analyticOnNhd isOpen_univ

/-- The `s = 0` coordinate is reached at `z = I/2`. -/
lemma half_add_I_mul_I_div_two :
    (1 / 2 : ℂ) + Complex.I * (Complex.I / 2) = 0 := by
  have h : Complex.I * (Complex.I / 2) = (-1 / 2 : ℂ) := by
    calc
      Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = (-1 : ℂ) / 2 := by rw [Complex.I_mul_I]
  rw [h]
  norm_num

/-- The pole-cancelled entire endpoint is not the zero function. -/
theorem xiEntire_I_div_two :
    HurwitzBridge.xiEntire (Complex.I / 2) = (1 / 2 : ℂ) := by
  unfold HurwitzBridge.xiEntire
  rw [half_add_I_mul_I_div_two]
  norm_num

/-- A concrete nonzero witness for the pole-cancelled entire endpoint. -/
theorem xiEntire_nontrivial : ∃ z : ℂ, HurwitzBridge.xiEntire z ≠ 0 := by
  refine ⟨Complex.I / 2, ?_⟩
  rw [xiEntire_I_div_two]
  norm_num

/-- Away from the completed-zeta pole and the Gamma-factor exceptional point,
the pole-cancelled entire endpoint is the usual prefactor times raw `Ξ`. -/
theorem xiEntire_eq_prefactor_mul_riemannXi_of_ne
    (z : ℂ)
    (h0 : (1 / 2 + Complex.I * z : ℂ) ≠ 0)
    (h1 : (1 / 2 + Complex.I * z : ℂ) ≠ 1) :
    HurwitzBridge.xiEntire z =
      (1 / 2) * ((1 / 2 + Complex.I * z) * (1 / 2 + Complex.I * z - 1) *
        RHReduction.riemannXi z) := by
  unfold HurwitzBridge.xiEntire RHReduction.riemannXi
  rw [← HurwitzBridge.xi_pole_cancel (1 / 2 + Complex.I * z) h0 h1]

/-- Every regular raw-`Ξ` zero is a zero of the pole-cancelled entire endpoint. -/
theorem xiEntire_eq_zero_of_riemannXiRegularZero {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z) :
    HurwitzBridge.xiEntire z = 0 := by
  rcases hz with ⟨hXi, hGamma, hne1⟩
  have hne0 : (1 / 2 + Complex.I * z : ℂ) ≠ 0 := by
    intro hs0
    apply hGamma
    rw [Complex.Gammaℝ_eq_zero_iff]
    exact ⟨0, by simpa using hs0⟩
  rw [xiEntire_eq_prefactor_mul_riemannXi_of_ne z hne0 hne1, hXi]
  ring

/-- Reality of all pole-cancelled `Ξ` zeros implies reality of regular raw-`Ξ` zeros. -/
theorem regularXiZerosReal_of_xiEntireZerosReal
    (H : ∀ z : ℂ, HurwitzBridge.xiEntire z = 0 → z.im = 0) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  intro z hz
  exact H z (xiEntire_eq_zero_of_riemannXiRegularZero hz)

/--
Concrete sequence form of the determinant Hurwitz bridge.

This is the proved analytic transfer for the determinant route: a sequence of
entire real-zero determinants that converges locally uniformly to the
pole-cancelled entire `Ξ` endpoint forces every regular raw-`Ξ` zero to be real.
The open determinant burden is exactly `hconv`, plus concrete determinant
analyticity; nontriviality of the `Ξ` endpoint is proved by `xiEntire_nontrivial`.
-/
theorem regularXiZerosReal_of_realZeros_and_tendsto_xiEntire_sequence
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hconv : TendstoLocallyUniformlyOn (fun n => D.determinant (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  refine regularXiZerosReal_of_xiEntireZerosReal ?_
  exact HurwitzBridge.hurwitz_realRooted_transfer hFa
    (fun n z hz => hreal (scale n) z hz)
    xiEntire_analyticOnNhd_univ hconv xiEntire_nontrivial

/-- Concrete sequence form of the determinant Hurwitz route all the way to
mathlib's `RiemannHypothesis`.  The load-bearing open input is the actual
locally-uniform convergence of the determinant sequence to `xiEntire`. -/
theorem riemannHypothesis_of_realZeros_and_tendsto_xiEntire_sequence
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hconv : TendstoLocallyUniformlyOn (fun n => D.determinant (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (D.regularXiZerosReal_of_realZeros_and_tendsto_xiEntire_sequence
      scale hFa hreal hconv)

/--
Derivative/basepoint form of the determinant Hurwitz bridge.

Instead of assuming the full locally-uniform convergence row directly, it is
enough to prove locally-uniform convergence of determinant derivatives to
`deriv xiEntire`, plus convergence at a fixed basepoint `w₀`.
-/
theorem regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => D.determinant (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀))) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  have hFdiff : ∀ᶠ n in Filter.atTop,
      Differentiable ℂ (D.determinant (scale n)) :=
    Filter.Eventually.of_forall fun n z =>
      (hFa n z (Set.mem_univ z)).differentiableAt
  have hconv : TendstoLocallyUniformlyOn (fun n => D.determinant (scale n))
      HurwitzBridge.xiEntire Filter.atTop Set.univ :=
    _root_.JensenLadder.DerivativeBasepointConvergence.tendstoLocallyUniformlyOn_of_deriv_tendstoLocallyUniformlyOn_univ_basepoint
      (fun n => D.determinant (scale n)) HurwitzBridge.xiEntire w₀
      hFdiff HurwitzBridge.xiEntire_differentiable hderiv hbase
  exact D.regularXiZerosReal_of_realZeros_and_tendsto_xiEntire_sequence
    scale hFa hreal hconv

/-- Determinant real-zero data plus derivative/basepoint convergence proves
mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => D.determinant (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀))) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
      scale w₀ hFa hreal hderiv hbase)

/-- Basepoint-`0` specialization of the derivative/basepoint determinant
Hurwitz bridge. -/
theorem regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => D.determinant (scale n) 0) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire 0))) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
  D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
    scale 0 hFa hreal hderiv hbase

/-- Basepoint-`0` specialization of the determinant derivative/basepoint
route all the way to mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_realZeros_and_deriv_tendsto_xiEntire_sequence
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hbase : Tendsto (fun n => D.determinant (scale n) 0) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire 0))) :
    RiemannHypothesis :=
  D.riemannHypothesis_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
    scale 0 hFa hreal hderiv hbase

/--
Scalar basepoint-normalization consumer.

If the finite basepoint values are eventually equal to a product of two declared
normalization factors and each factor converges to its target value, then the
basepoint values converge to the target product.  The nonzero/legal-basepoint
condition belongs to the surrounding normalization contract; the scalar
convergence itself only uses multiplication of limits.
-/
theorem basepointValue_tendsto_of_factor_tendsto
    {ι : Type*} {l : Filter ι}
    (F C G : ι → ℂ) (Clim Glim T : ℂ)
    (hfactor : ∀ᶠ n in l, F n = C n * G n)
    (hT : T = Clim * Glim)
    (hC : Tendsto C l (𝓝 Clim))
    (hG : Tendsto G l (𝓝 Glim)) :
    Tendsto F l (𝓝 T) := by
  have hprod : Tendsto (fun n => C n * G n) l (𝓝 (Clim * Glim)) := hC.mul hG
  have hcongr : F =ᶠ[l] fun n => C n * G n := hfactor
  simpa [hT] using hprod.congr' hcongr.symm

/--
Scalar ratio-normalization consumer.

If the target basepoint value is nonzero and the normalized ratio `F_n / T`
converges to `1`, then the finite basepoint values converge to `T`.
-/
theorem basepointValue_tendsto_of_ratio_tendsto
    {ι : Type*} {l : Filter ι}
    (F : ι → ℂ) (T : ℂ)
    (hT : T ≠ 0)
    (hratio : Tendsto (fun n => F n / T) l (𝓝 1)) :
    Tendsto F l (𝓝 T) := by
  have hmul : Tendsto (fun n => (F n / T) * T) l (𝓝 (1 * T)) :=
    hratio.mul tendsto_const_nhds
  have hcongr : (fun n => (F n / T) * T) =ᶠ[l] F :=
    Filter.Eventually.of_forall fun n => by
      field_simp [hT]
  simpa [one_mul] using hmul.congr' hcongr

/--
First-derivative centering excludes a residual exponential slope.

This is the scalar normalization row used when a reconstruction has left a
possible factor `exp(a z)`: if its derivative at the origin is forced to vanish,
then the slope `a` is zero.
-/
theorem residualExponential_slope_eq_zero_of_deriv_zero
    (a : ℂ)
    (hcenter : deriv (fun z : ℂ => Complex.exp (a * z)) 0 = 0) :
    a = 0 := by
  have hderiv : deriv (fun z : ℂ => Complex.exp (a * z)) 0 = a := by
    have hlin : HasDerivAt (fun z : ℂ => a * z) a 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul a
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
        (Complex.exp (a * 0) * a) 0 :=
      hlin.cexp
    simpa using hexp.deriv
  rw [hderiv] at hcenter
  exact hcenter

/-- Once first-derivative centering kills the slope, the residual exponential
factor is identically `1`. -/
theorem residualExponential_eq_one_of_deriv_zero
    (a : ℂ)
    (hcenter : deriv (fun z : ℂ => Complex.exp (a * z)) 0 = 0) :
    ∀ z : ℂ, Complex.exp (a * z) = 1 := by
  intro z
  have ha : a = 0 := residualExponential_slope_eq_zero_of_deriv_zero a hcenter
  simp [ha]

/--
Evenness under the functional-equation reflection excludes a residual
exponential slope.

If the leftover scalar factor `exp(a z)` is invariant under `z ↦ -z`, then
differentiating at the origin gives `-a = a`, hence `a = 0`.
-/
theorem residualExponential_slope_eq_zero_of_even
    (a : ℂ)
    (heven : ∀ z : ℂ, Complex.exp (a * (-z)) = Complex.exp (a * z)) :
    a = 0 := by
  have hfun : (fun z : ℂ => Complex.exp (a * (-z))) =
      (fun z : ℂ => Complex.exp (a * z)) := by
    funext z
    exact heven z
  have hderiv_eq : deriv (fun z : ℂ => Complex.exp (a * (-z))) 0 =
      deriv (fun z : ℂ => Complex.exp (a * z)) 0 := by
    simpa using congrArg (fun f : ℂ → ℂ => deriv f 0) hfun
  have hleft : deriv (fun z : ℂ => Complex.exp (a * (-z))) 0 = -a := by
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).neg
    have hlin : HasDerivAt (fun z : ℂ => a * (-z)) (-a) 0 := by
      simpa using hneg.const_mul a
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (a * (-z)))
        (Complex.exp (a * (-0)) * (-a)) 0 :=
      hlin.cexp
    simpa using hexp.deriv
  have hright : deriv (fun z : ℂ => Complex.exp (a * z)) 0 = a := by
    have hlin : HasDerivAt (fun z : ℂ => a * z) a 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul a
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
        (Complex.exp (a * 0) * a) 0 :=
      hlin.cexp
    simpa using hexp.deriv
  have hneg_eq : -a = a := by
    rw [hleft, hright] at hderiv_eq
    exact hderiv_eq
  exact neg_eq_self.mp hneg_eq

/-- Once reflection-evenness kills the slope, the residual exponential factor is
identically `1`. -/
theorem residualExponential_eq_one_of_even
    (a : ℂ)
    (heven : ∀ z : ℂ, Complex.exp (a * (-z)) = Complex.exp (a * z)) :
    ∀ z : ℂ, Complex.exp (a * z) = 1 := by
  intro z
  have ha : a = 0 := residualExponential_slope_eq_zero_of_even a heven
  simp [ha]

/--
Derivative/basepoint determinant Hurwitz bridge with the basepoint convergence
discharged by a declared two-factor normalization.
-/
theorem regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_factor_tendsto_at_basepoint
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (C G : ℕ → ℂ) (Clim Glim : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hfactor : ∀ᶠ n in Filter.atTop, D.determinant (scale n) w₀ = C n * G n)
    (hXiFactor : HurwitzBridge.xiEntire w₀ = Clim * Glim)
    (hC : Tendsto C Filter.atTop (𝓝 Clim))
    (hG : Tendsto G Filter.atTop (𝓝 Glim)) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  have hbase : Tendsto (fun n => D.determinant (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀)) :=
    basepointValue_tendsto_of_factor_tendsto
      (fun n => D.determinant (scale n) w₀) C G Clim Glim
      (HurwitzBridge.xiEntire w₀) hfactor hXiFactor hC hG
  exact
    D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
      scale w₀ hFa hreal hderiv hbase

/--
Determinant real-zero data, derivative convergence, and a two-factor basepoint
normalization prove mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_factor_tendsto_at_basepoint
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (C G : ℕ → ℂ) (Clim Glim : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hfactor : ∀ᶠ n in Filter.atTop, D.determinant (scale n) w₀ = C n * G n)
    (hXiFactor : HurwitzBridge.xiEntire w₀ = Clim * Glim)
    (hC : Tendsto C Filter.atTop (𝓝 Clim))
    (hG : Tendsto G Filter.atTop (𝓝 Glim)) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_factor_tendsto_at_basepoint
      scale w₀ C G Clim Glim hFa hreal hderiv hfactor hXiFactor hC hG)

/--
Derivative/basepoint determinant Hurwitz bridge with the basepoint convergence
discharged by a nonzero target value and ratio normalization
`F_n(w₀) / xiEntire(w₀) -> 1`.
-/
theorem regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_basepoint_ratio_tendsto
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hXi_ne : HurwitzBridge.xiEntire w₀ ≠ 0)
    (hratio : Tendsto
      (fun n => D.determinant (scale n) w₀ / HurwitzBridge.xiEntire w₀)
      Filter.atTop (𝓝 1)) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 := by
  have hbase : Tendsto (fun n => D.determinant (scale n) w₀) Filter.atTop
      (𝓝 (HurwitzBridge.xiEntire w₀)) :=
    basepointValue_tendsto_of_ratio_tendsto
      (fun n => D.determinant (scale n) w₀)
      (HurwitzBridge.xiEntire w₀) hXi_ne hratio
  exact
    D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_at_basepoint
      scale w₀ hFa hreal hderiv hbase

/--
Determinant real-zero data, derivative convergence, and nonzero basepoint ratio
normalization prove mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_basepoint_ratio_tendsto
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (w₀ : ℂ)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hreal : D.AllZerosReal)
    (hderiv : TendstoLocallyUniformlyOn
      (fun n z => deriv (D.determinant (scale n)) z)
      (deriv HurwitzBridge.xiEntire) Filter.atTop Set.univ)
    (hXi_ne : HurwitzBridge.xiEntire w₀ ≠ 0)
    (hratio : Tendsto
      (fun n => D.determinant (scale n) w₀ / HurwitzBridge.xiEntire w₀)
      Filter.atTop (𝓝 1)) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (D.regularXiZerosReal_of_realZeros_and_deriv_tendsto_xiEntire_sequence_of_basepoint_ratio_tendsto
      scale w₀ hFa hreal hderiv hXi_ne hratio)

/--
Eigenvalue dictionary plus canonical-product control for a determinant sequence.

The finite dictionary rows say that the zeros of each finite determinant are
exactly represented by real eigenheights.  This is still not enough to identify
the limiting zero set.  The load-bearing analytic row is
`canonicalProductControl`: it stands for the genus/product/tail estimates that
upgrade finite eigenvalue data to locally-uniform convergence of normalized
determinants to the pole-cancelled `Ξ` endpoint.
-/
structure EigenvalueProductBridge
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale) where
  EigenLabel : D.Scale → Type u
  eigenHeight : ∀ a : D.Scale, EigenLabel a → ℝ
  eigen_zero :
    ∀ (a : D.Scale) (γ : EigenLabel a),
      D.determinant a (eigenHeight a γ : ℂ) = 0
  zero_complete :
    ∀ (a : D.Scale) (z : ℂ), D.determinant a z = 0 →
      ∃ γ : EigenLabel a, z = (eigenHeight a γ : ℂ)
  canonicalProductControl : Prop
  locallyUniformToXi_of_canonicalProductControl :
    canonicalProductControl →
      TendstoLocallyUniformlyOn (fun n => D.determinant (scale n))
        HurwitzBridge.xiEntire Filter.atTop Set.univ

namespace EigenvalueProductBridge

/-- A finite real eigenvalue dictionary forces every finite determinant zero to
be real. -/
theorem allZerosReal
    {D : DeterminantApproximants.{u}} {scale : ℕ → D.Scale}
    (B : EigenvalueProductBridge D scale) :
    D.AllZerosReal := by
  intro a z hz
  rcases B.zero_complete a z hz with ⟨γ, hzγ⟩
  rw [hzγ]
  simp

/--
Eigenvalue dictionary plus canonical-product control supplies the concrete
determinant Hurwitz bridge.

The analytic substance remains the `canonicalProductControl` row: it must turn
finite eigenvalue/product data into actual locally-uniform determinant
convergence.
-/
theorem regularXiZerosReal
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (B : EigenvalueProductBridge D scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hcontrol : B.canonicalProductControl) :
    ∀ z : ℂ, RHReduction.riemannXiRegularZero z → z.im = 0 :=
  D.regularXiZerosReal_of_realZeros_and_tendsto_xiEntire_sequence
    scale hFa B.allZerosReal
    (B.locallyUniformToXi_of_canonicalProductControl hcontrol)

/-- Eigenvalue dictionary plus canonical-product control proves mathlib's
`RiemannHypothesis` through the determinant Hurwitz route. -/
theorem riemannHypothesis
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (B : EigenvalueProductBridge D scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    (hcontrol : B.canonicalProductControl) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (B.regularXiZerosReal D scale hFa hcontrol)

/--
A non-real regular `Ξ` zero refutes the canonical-product/tail-control row,
provided the finite determinant zeros are exactly represented by real
eigenheights.
-/
theorem not_canonicalProductControl_of_nonrealRegularXiZero
    (D : DeterminantApproximants.{u})
    (scale : ℕ → D.Scale)
    (B : EigenvalueProductBridge D scale)
    (hFa : ∀ n, AnalyticOnNhd ℂ (D.determinant (scale n)) Set.univ)
    {z : ℂ}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    ¬ B.canonicalProductControl := by
  intro hcontrol
  exact hzim (B.regularXiZerosReal D scale hFa hcontrol z hz)

end EigenvalueProductBridge

/--
Packaged determinant certificate whose convergence row is refined as an
eigenvalue dictionary plus canonical-product/tail control.
-/
structure EigenvalueProductRHCertificate where
  approximants : DeterminantApproximants.{u}
  scale : ℕ → approximants.Scale
  bridge : EigenvalueProductBridge approximants scale
  determinantAnalytic :
    ∀ n, AnalyticOnNhd ℂ (approximants.determinant (scale n)) Set.univ
  canonicalProductControl : bridge.canonicalProductControl

namespace EigenvalueProductRHCertificate

/-- A packaged eigenvalue/product determinant certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : EigenvalueProductRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.bridge.riemannHypothesis cert.approximants cert.scale
    cert.determinantAnalytic cert.canonicalProductControl

end EigenvalueProductRHCertificate

/--
The determinant-route Hurwitz row.

`locallyUniformToXi` is the analytic estimate: normalized determinants converge
to `RHReduction.riemannXi` locally uniformly on compact subsets, with the
normalization and nonzero-limit hypotheses included in the external theorem.
The transfer field is the Hurwitz/LP-closure consequence needed by the RH
handoff.
-/
structure HurwitzConvergence (D : DeterminantApproximants.{u}) where
  locallyUniformToXi : Prop
  regularXiZerosReal_of_realZeros_and_locallyUniform :
    D.AllZerosReal -> locallyUniformToXi ->
      forall z : Complex, RHReduction.riemannXiRegularZero z -> z.im = 0

namespace HurwitzConvergence

/-- Repackage determinant convergence as the existing C-vS Hurwitz row. -/
def toCVSHurwitzXiConvergence
    {D : DeterminantApproximants.{u}}
    (H : HurwitzConvergence D) :
    HurwitzXiConvergence D.toFiniteScaleApproximants where
  convergesToXi := H.locallyUniformToXi
  regularXiZerosReal_of_approximantsReal_and_convergence := by
    intro hreal hconv z hz
    exact H.regularXiZerosReal_of_realZeros_and_locallyUniform
      (D.allZerosReal_of_allApproximantZerosReal hreal) hconv z hz

end HurwitzConvergence

/--
Finite determinant real-zero data plus the determinant Hurwitz row proves
mathlib's `RiemannHypothesis`.

The hard input is `hconv`: the locally-uniform convergence theorem.
-/
theorem riemannHypothesis_of_allZerosReal_and_locallyUniform
    (D : DeterminantApproximants.{u})
    (H : D.HurwitzConvergence)
    (hreal : D.AllZerosReal)
    (hconv : H.locallyUniformToXi) :
    RiemannHypothesis :=
  (RHReduction.riemannHypothesis_iff_regular_riemannXi_zeros_real).2
    (H.regularXiZerosReal_of_realZeros_and_locallyUniform hreal hconv)

/--
A non-real regular `Xi` zero refutes the locally-uniform determinant convergence
row, assuming every finite determinant has only real zeros.
-/
theorem not_locallyUniformToXi_of_nonrealRegularXiZero_and_allZerosReal
    (D : DeterminantApproximants.{u})
    (H : D.HurwitzConvergence)
    (hreal : D.AllZerosReal)
    {z : Complex}
    (hz : RHReduction.riemannXiRegularZero z)
    (hzim : z.im ≠ 0) :
    Not H.locallyUniformToXi := by
  intro hconv
  exact hzim
    (H.regularXiZerosReal_of_realZeros_and_locallyUniform hreal hconv z hz)

/-- Packaged determinant-route RH certificate. -/
structure DeterminantHurwitzRHCertificate where
  approximants : DeterminantApproximants.{u}
  convergence : approximants.HurwitzConvergence
  allZerosReal : approximants.AllZerosReal
  locallyUniformToXi : convergence.locallyUniformToXi

namespace DeterminantHurwitzRHCertificate

/-- The packaged determinant row as the generic C-vS convergence interface. -/
def cvsConvergence
    (cert : DeterminantHurwitzRHCertificate.{u}) :
    HurwitzXiConvergence cert.approximants.toFiniteScaleApproximants :=
  cert.convergence.toCVSHurwitzXiConvergence

/-- A packaged determinant Hurwitz certificate proves mathlib's RH. -/
theorem riemannHypothesis
    (cert : DeterminantHurwitzRHCertificate.{u}) :
    RiemannHypothesis :=
  cert.approximants.riemannHypothesis_of_allZerosReal_and_locallyUniform
    cert.convergence cert.allZerosReal cert.locallyUniformToXi

end DeterminantHurwitzRHCertificate

end DeterminantApproximants

end DeterminantHurwitzRoute
end JensenLadder
