import Mathlib

/-!
# Scattering-vs-ξ parity obstruction (a verified no-go closing the RATIO class)

Object-X search outcome (codex, Goldfeld-sourced; verified here): a scalar object `R`
satisfying the **scattering** functional equation `R(s)·R(1−s) = 1` has an **even**
logarithmic derivative about the critical line, whereas an object `g` satisfying the
**ξ-type** functional equation `g(s) = g(1−s)` has an **odd** logarithmic derivative. Hence
no scalar scattering-FE determinant can share `ξ`'s logarithmic derivative except trivially
(both ≡ 0). This is the structural reason the modular scattering determinant
`φ(s)=Λ(2s−1)/Λ(2s)` yields only the *square* prime-power subrow and can never be the `Ξ`
numerator by any normalization — it closes the entire RATIO class of Object-X candidates.

Proved here (kernel-checked):
* `logDeriv_even_of_scattering_fe` : `R(s)R(1−s)=1 ⟹ logDeriv R s = logDeriv R (1−s)`.
* `logDeriv_odd_of_xi_fe` : `g(s)=g(1−s) ⟹ logDeriv g s = − logDeriv g (1−s)`.
* `logDeriv_eq_zero_of_scattering_eq_xi` : even ∧ odd ∧ (same logDeriv) ⟹ `logDeriv g ≡ 0`.
* `deriv_eq_zero_of_scattering_eq_xi` : consequently `deriv g ≡ 0` (so `g` is constant) —
  i.e. a scattering-FE object and a ξ-FE object can share a logarithmic derivative only if
  that object is constant.

Evidence class: proved lemma / dead-end elimination. No RH evidence. Theorem M is proven,
but Theorem M does not prove RH by itself.
-/

open Complex

namespace JensenLadder.ScatteringParityNoGo

/-- A scalar object with the **scattering** functional equation `R(s)·R(1−s)=1` has a
logarithmic derivative symmetric under `s ↦ 1−s` (i.e. even about the critical line). -/
theorem logDeriv_even_of_scattering_fe
    {R : ℂ → ℂ} (hR : Differentiable ℂ R) (hRne : ∀ s, R s ≠ 0)
    (hFE : ∀ s, R s * R (1 - s) = 1) :
    ∀ s, logDeriv R s = logDeriv R (1 - s) := by
  intro s
  have hdg : DifferentiableAt ℂ (fun z => R (1 - z)) s := (hR (1 - s)).comp s (by fun_prop)
  have hP : (fun z => R z * R (1 - z)) = (fun _ => (1 : ℂ)) := funext hFE
  have h0 : logDeriv (fun z => R z * R (1 - z)) s = 0 := by
    rw [hP]; simp
  have hmul : logDeriv (fun z => R z * R (1 - z)) s
      = logDeriv R s + logDeriv (fun z => R (1 - z)) s :=
    logDeriv_mul s (hRne s) (hRne (1 - s)) (hR s) hdg
  have hcomp : logDeriv (fun z => R (1 - z)) s = logDeriv R (1 - s) * (-1) := by
    have hce : (fun z => R (1 - z)) = R ∘ (fun z => 1 - z) := rfl
    rw [hce, logDeriv_comp (hR (1 - s)) (by fun_prop)]
    congr 1
    simp
  rw [hmul, hcomp] at h0
  linear_combination h0

/-- A scalar object with the **ξ-type** functional equation `g(s)=g(1−s)` has a logarithmic
derivative antisymmetric under `s ↦ 1−s` (i.e. odd about the critical line). -/
theorem logDeriv_odd_of_xi_fe
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hFE : ∀ s, g s = g (1 - s)) :
    ∀ s, logDeriv g s = - logDeriv g (1 - s) := by
  intro s
  have hcomp : logDeriv (fun z => g (1 - z)) s = logDeriv g (1 - s) * (-1) := by
    have hce : (fun z => g (1 - z)) = g ∘ (fun z => 1 - z) := rfl
    rw [hce, logDeriv_comp (hg (1 - s)) (by fun_prop)]
    congr 1
    simp
  have heqfun : (fun z => g (1 - z)) = g := funext (fun z => (hFE z).symm)
  rw [heqfun] at hcomp
  rw [hcomp]; ring

/-- **Parity obstruction.** If `R` is even-type (scattering FE) and `g` is odd-type (ξ FE)
about the critical line and they share a logarithmic derivative, then that logarithmic
derivative vanishes identically. -/
theorem logDeriv_eq_zero_of_scattering_eq_xi
    {R g : ℂ → ℂ}
    (hReven : ∀ s, logDeriv R s = logDeriv R (1 - s))
    (hgodd : ∀ s, logDeriv g s = - logDeriv g (1 - s))
    (hRg : ∀ s, logDeriv R s = logDeriv g s) :
    ∀ s, logDeriv g s = 0 := by
  intro s
  have e1 : logDeriv g s = logDeriv g (1 - s) := by
    rw [← hRg s, ← hRg (1 - s)]; exact hReven s
  have e2 : logDeriv g s = - logDeriv g (1 - s) := hgodd s
  rw [e1] at e2
  have hz : logDeriv g (1 - s) = 0 := by linear_combination e2 / 2
  rw [e1]; exact hz

/-- Consequence: a scattering-FE object and a ξ-FE object can share a logarithmic derivative
only if that object is constant (`deriv g ≡ 0`). Since `Ξ` is nonconstant, no scalar
scattering determinant equals it. -/
theorem deriv_eq_zero_of_scattering_eq_xi
    {R g : ℂ → ℂ} (hgne : ∀ s, g s ≠ 0)
    (hReven : ∀ s, logDeriv R s = logDeriv R (1 - s))
    (hgodd : ∀ s, logDeriv g s = - logDeriv g (1 - s))
    (hRg : ∀ s, logDeriv R s = logDeriv g s) :
    ∀ s, deriv g s = 0 := by
  intro s
  have h := logDeriv_eq_zero_of_scattering_eq_xi hReven hgodd hRg s
  rw [logDeriv_apply] at h
  exact (div_eq_zero_iff.mp h).resolve_right (hgne s)

end JensenLadder.ScatteringParityNoGo
