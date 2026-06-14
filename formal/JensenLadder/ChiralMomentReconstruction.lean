import JensenLadder.ChiralStieltjesTrace

/-!
# Chiral moment reconstruction

This module formalizes the finite determinant-reconstruction row behind the
chiral squared Fredholm target.  On any open preconnected zero-free domain,
equal logarithmic derivatives determine two determinants up to a scalar; a
single basepoint fixes that scalar.

For the finite Fredholm products from `ChiralStieltjesTrace`, this says that a
same-carrier Stieltjes trace row plus the normalization `Det(0)=Target(0)`
leaves no residual zero-free factor.

This file does not construct a trace-class operator, a Fredholm determinant,
a moment problem, a Hadamard product, or a zeta carrier.  It is a finite/local
reconstruction consumer only.

Evidence class: proved lemma / formal artifact.  Theorem M is proven, but
Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace ChiralMomentReconstruction

open Set

/--
On a connected zero-free domain, equality of logarithmic derivatives plus one
basepoint equality forces equality of the functions.
-/
theorem eqOn_of_logDeriv_eqOn_and_basepoint
    {f g : ℂ → ℂ} {s : Set ℂ} {z0 : ℂ}
    (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (hsOpen : IsOpen s) (hsConn : IsPreconnected s)
    (hgn : ∀ z ∈ s, g z ≠ 0) (hfn : ∀ z ∈ s, f z ≠ 0)
    (hlog : EqOn (logDeriv f) (logDeriv g) s)
    (hz0 : z0 ∈ s) (hbase : f z0 = g z0) :
    EqOn f g s := by
  rcases (logDeriv_eqOn_iff hf hg hsOpen hsConn hgn hfn).1 hlog with
    ⟨c, _hc0, hscale⟩
  have hg0 : g z0 ≠ 0 := hgn z0 hz0
  have hscale0 : f z0 = c • g z0 := hscale hz0
  rw [hbase] at hscale0
  have hmul : c * g z0 = 1 * g z0 := by
    rw [smul_eq_mul] at hscale0
    simpa using hscale0.symm
  have hc : c = 1 := mul_right_cancel₀ hg0 hmul
  intro z hz
  have hzscale : f z = c • g z := hscale hz
  simpa [hc] using hzscale

/-- Whole-plane specialization of
`eqOn_of_logDeriv_eqOn_and_basepoint`. -/
theorem eq_of_logDeriv_eq_and_basepoint
    {f g : ℂ → ℂ} {z0 : ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgn : ∀ z, g z ≠ 0) (hfn : ∀ z, f z ≠ 0)
    (hlog : ∀ z, logDeriv f z = logDeriv g z)
    (hbase : f z0 = g z0) :
    f = g := by
  funext z
  exact eqOn_of_logDeriv_eqOn_and_basepoint
    (s := Set.univ) (z0 := z0)
    hf.differentiableOn hg.differentiableOn
    isOpen_univ isPreconnected_univ
    (by intro z _hz; exact hgn z)
    (by intro z _hz; exact hfn z)
    (by intro z _hz; exact hlog z)
    (Set.mem_univ z0) hbase (Set.mem_univ z)

/--
A zero-free same-trace reconstruction package.

`determinant_trace` and `target_trace` assert that both functions have the same
Stieltjes/log-derivative trace on the same domain.  The theorem below shows
that the determinant and target are then identical on that domain after one
basepoint value is fixed.
-/
structure ZeroFreeTraceReconstruction where
  domain : Set ℂ
  basepoint : ℂ
  determinant : ℂ → ℂ
  target : ℂ → ℂ
  trace : ℂ → ℂ
  determinant_differentiable : DifferentiableOn ℂ determinant domain
  target_differentiable : DifferentiableOn ℂ target domain
  domain_open : IsOpen domain
  domain_preconnected : IsPreconnected domain
  determinant_ne_zero : ∀ z ∈ domain, determinant z ≠ 0
  target_ne_zero : ∀ z ∈ domain, target z ≠ 0
  determinant_trace : EqOn (fun z => -logDeriv determinant z) trace domain
  target_trace : EqOn (fun z => -logDeriv target z) trace domain
  basepoint_mem : basepoint ∈ domain
  basepoint_eq : determinant basepoint = target basepoint

namespace ZeroFreeTraceReconstruction

/-- Same trace rows imply equality of logarithmic derivatives. -/
theorem logDeriv_eqOn (R : ZeroFreeTraceReconstruction) :
    EqOn (logDeriv R.determinant) (logDeriv R.target) R.domain := by
  intro z hz
  have hdet := R.determinant_trace hz
  have htgt := R.target_trace hz
  have hneg : -logDeriv R.determinant z = -logDeriv R.target z :=
    hdet.trans htgt.symm
  exact neg_injective hneg

/-- A zero-free same-trace row plus a basepoint reconstructs the determinant. -/
theorem determinant_eqOn_target (R : ZeroFreeTraceReconstruction) :
    EqOn R.determinant R.target R.domain :=
  eqOn_of_logDeriv_eqOn_and_basepoint
    R.determinant_differentiable R.target_differentiable
    R.domain_open R.domain_preconnected
    R.target_ne_zero R.determinant_ne_zero
    R.logDeriv_eqOn R.basepoint_mem R.basepoint_eq

end ZeroFreeTraceReconstruction

end ChiralMomentReconstruction

namespace SquaredDeterminantSpectralProduct
namespace FiniteSquaredSpectrum

open scoped BigOperators

/--
Finite Fredholm specialization: if a target has the same Fredholm Stieltjes
trace as `S.fredholmDeterminant` on a zero-free connected domain and agrees at
one basepoint, then it is the same determinant on that domain.
-/
theorem fredholmDeterminant_eqOn_of_same_trace_and_basepoint
    (S : FiniteSquaredSpectrum.{u}) {target : ℂ → ℂ}
    {s : Set ℂ} {z0 : ℂ}
    (htarget : DifferentiableOn ℂ target s)
    (hsOpen : IsOpen s) (hsConn : IsPreconnected s)
    (hoff : ∀ z ∈ s, S.FredholmOffSpectrum z)
    (htarget_ne : ∀ z ∈ s, target z ≠ 0)
    (htrace : Set.EqOn (fun z => -logDeriv target z) S.fredholmResolventTrace s)
    (hz0 : z0 ∈ s)
    (hbase : S.fredholmDeterminant z0 = target z0) :
    Set.EqOn S.fredholmDeterminant target s := by
  classical
  letI := S.fintype
  exact
    (ChiralMomentReconstruction.ZeroFreeTraceReconstruction.determinant_eqOn_target {
      domain := s
      basepoint := z0
      determinant := S.fredholmDeterminant
      target := target
      trace := S.fredholmResolventTrace
      determinant_differentiable := by
        unfold fredholmDeterminant
        fun_prop
      target_differentiable := htarget
      domain_open := hsOpen
      domain_preconnected := hsConn
      determinant_ne_zero := by
        intro z hz
        exact S.fredholmDeterminant_ne_zero_of_fredholmOffSpectrum
          (hoff z hz)
      target_ne_zero := htarget_ne
      determinant_trace := by
        intro z hz
        exact S.neg_logDeriv_fredholmDeterminant_eq_fredholmResolventTrace
          (hoff z hz)
      target_trace := htrace
      basepoint_mem := hz0
      basepoint_eq := hbase
    })

end FiniteSquaredSpectrum
end SquaredDeterminantSpectralProduct
end JensenLadder
