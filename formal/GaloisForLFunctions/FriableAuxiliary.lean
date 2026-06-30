import GaloisForLFunctions.SmoothNumbers

/-!
# Friable Dirichlet auxiliary: derivative anchor at `s = 1` (Tier A)

This file formalizes the elementary derivative identity from
`docs/drafts/pipeline/2-fully-proven/friable-dirichlet-auxiliary.md`.

We use the exponential model `n^{-s} = exp(-s log n)`, which is the analytic
term used in the card's `s = 1` reduction. The main theorem
`iteratedDeriv_friableExponentDirichletExp_at_one` states that a finitely
supported friable auxiliary indexed by prime exponent vectors has

`F^(T)(1) = (-1)^T Σ_m λ_m (Σ_p m_p log p)^T / n_m`,

with `n_m = primeProduct m`. This is the derivative half of the card's
obstruction-C reduction. The multinomial expansion into degree-`T` log monomials
and any Schanuel/algebraic-independence lower bound are not formalized here.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The exponential model for a finite Dirichlet polynomial with natural-number frequencies. -/
def friableDirichletExp (P : ℕ →₀ ℂ) (s : ℂ) : ℂ :=
  P.sum fun n c => c * Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))

lemma contDiff_exp_neg_mul_log (T : ℕ) (L : ℂ) (z : ℂ) :
    ContDiffAt ℂ (T : WithTop ℕ∞) (fun z : ℂ => Complex.exp (-(z * L))) z := by
  have h : ContDiff ℂ ⊤ (fun z : ℂ => Complex.exp (-(z * L))) := by
    have hlin : ContDiff ℂ ⊤ (fun z : ℂ => -(z * L)) := by
      have hid : ContDiff ℂ ⊤ (fun z : ℂ => z) := contDiff_id
      have hc : ContDiff ℂ ⊤ (fun _z : ℂ => L) := contDiff_const
      simpa using (hid.mul hc).neg
    exact hlin.cexp
  exact h.contDiffAt.of_le le_top

theorem iteratedDeriv_exp_neg_mul_log_fun (T : ℕ) (L : ℂ) :
    iteratedDeriv T (fun z : ℂ => Complex.exp (-(z * L))) =
      fun z : ℂ => (-L) ^ T * Complex.exp (-(z * L)) := by
  induction T with
  | zero =>
      funext z
      simp
  | succ T ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      have hlin : HasDerivAt (fun z : ℂ => -(z * L)) (-L) z := by
        have hid : HasDerivAt (fun z : ℂ => z) 1 z := hasDerivAt_id z
        simpa using (hid.mul_const L).neg
      have hdiff : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-(z * L))) z :=
        hlin.cexp.differentiableAt
      rw [deriv_const_mul ((-L) ^ T) hdiff]
      rw [hlin.cexp.deriv]
      ring

/-- Iterated derivative of `exp(-sL)`. -/
theorem iteratedDeriv_exp_neg_mul_log (T : ℕ) (L s : ℂ) :
    iteratedDeriv T (fun z : ℂ => Complex.exp (-(z * L))) s =
      (-L) ^ T * Complex.exp (-(s * L)) := by
  rw [iteratedDeriv_exp_neg_mul_log_fun T L]

/-- At `s=1`, `exp(-log n)=n⁻¹` for nonzero natural frequencies. -/
theorem exp_neg_real_log_nat (n : ℕ) (hn : n ≠ 0) :
    Complex.exp (-(Real.log (n : ℝ) : ℂ)) = ((n : ℂ)⁻¹) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : ((Real.log (n : ℝ) : ℂ)) = Complex.log (n : ℂ) := by
    have h := Complex.ofReal_log hnpos.le
    rw [show ((n : ℝ) : ℂ) = (n : ℂ) by norm_num] at h
    exact h
  rw [hlog]
  rw [Complex.exp_neg]
  rw [Complex.exp_log hne]

/-- Single-frequency derivative formula at `s=1`:
`d^T/ds^T exp(-s log n)|_{s=1} = (-1)^T (log n)^T / n`. -/
theorem iteratedDeriv_nat_dirichlet_at_one (T n : ℕ) (hn : n ≠ 0) :
    iteratedDeriv T (fun z : ℂ => Complex.exp (-(z * (Real.log (n : ℝ) : ℂ)))) 1 =
      (-1 : ℂ) ^ T * (Real.log (n : ℝ) : ℂ) ^ T * ((n : ℂ)⁻¹) := by
  rw [iteratedDeriv_exp_neg_mul_log]
  rw [show -((Real.log (n : ℝ) : ℂ)) = (-1 : ℂ) * (Real.log (n : ℝ) : ℂ) by ring]
  rw [mul_pow]
  rw [show -((1 : ℂ) * (Real.log (n : ℝ) : ℂ)) = -(Real.log (n : ℝ) : ℂ) by ring]
  rw [exp_neg_real_log_nat n hn]

/-- Term-by-term derivative formula for a finite Dirichlet polynomial with nonzero
natural-number frequencies. -/
theorem iteratedDeriv_friableDirichletExp_at_one (T : ℕ) (P : ℕ →₀ ℂ)
    (hP : ∀ n ∈ P.support, n ≠ 0) :
    iteratedDeriv T (fun z : ℂ => friableDirichletExp P z) 1 =
      (-1 : ℂ) ^ T * P.sum (fun n c => c * (Real.log (n : ℝ) : ℂ) ^ T * ((n : ℂ)⁻¹)) := by
  unfold friableDirichletExp
  have hfun :
      (fun z : ℂ => P.sum fun n c => c * Complex.exp (-(z * (Real.log (n : ℝ) : ℂ)))) =
        (∑ n ∈ P.support, fun z : ℂ => P n * Complex.exp (-(z * (Real.log (n : ℝ) : ℂ)))) := by
    funext z
    rw [Finsupp.sum]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [iteratedDeriv_sum]
  · rw [Finsupp.sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [iteratedDeriv_const_mul]
    · rw [iteratedDeriv_nat_dirichlet_at_one T n (hP n hn)]
      ring
    · exact contDiff_exp_neg_mul_log T (Real.log (n : ℝ) : ℂ) 1
  · intro n hn
    have hc : ContDiffAt ℂ (T : WithTop ℕ∞) (fun _z : ℂ => P n) 1 := contDiffAt_const
    exact hc.mul (contDiff_exp_neg_mul_log T (Real.log (n : ℝ) : ℂ) 1)

/-- Casting the finite real prime-log dot product to `ℂ` may be done termwise. -/
lemma complex_cast_logPrime_sum (m : Nat.Primes →₀ ℕ) :
    (((m.sum fun p k => (k : ℝ) * Real.log (p : ℕ)) : ℝ) : ℂ) =
      m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ) := by
  change ((∑ p ∈ m.support, (m p : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ) =
      ∑ p ∈ m.support, (m p : ℂ) * (Real.log (p : ℕ) : ℂ)
  simp

/-- Multinomial word expansion of a finite prime-log dot product.

This is the Lean form of expanding `(Σ_p m_p log p)^T` into degree-`T`
prime-log monomials. The words `w : Fin T → Nat.Primes` encode the usual
multinomial coefficients by repetition before collecting like monomials. -/
theorem primeLogDot_pow_wordExpansion (m : Nat.Primes →₀ ℕ) (T : ℕ) :
    (m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin T => m.support),
        ∏ i : Fin T, ((m (w i) : ℂ) * (Real.log (w i : ℕ) : ℂ)) := by
  change (∑ p ∈ m.support, (m p : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin T => m.support),
        ∏ i : Fin T, ((m (w i) : ℂ) * (Real.log (w i : ℕ) : ℂ))
  exact Finset.sum_pow' m.support (fun p => (m p : ℂ) * (Real.log (p : ℕ) : ℂ)) T

/-- Friable auxiliary represented directly by prime-exponent vectors. -/
def friableExponentDirichletExp (P : (Nat.Primes →₀ ℕ) →₀ ℂ) (s : ℂ) : ℂ :=
  P.sum fun m c => c * Complex.exp (-(s * (Real.log (primeProduct m : ℝ) : ℂ)))

/-- Term-by-term derivative at `s=1` for the exponent-vector friable auxiliary,
with `log n_m` rewritten as `m · ℓ = Σ_p m_p log p`. -/
theorem iteratedDeriv_friableExponentDirichletExp_at_one
    (T : ℕ) (P : (Nat.Primes →₀ ℕ) →₀ ℂ) :
    iteratedDeriv T (fun z : ℂ => friableExponentDirichletExp P z) 1 =
      (-1 : ℂ) ^ T * P.sum (fun m c =>
        c * ((m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T) *
          ((primeProduct m : ℂ)⁻¹)) := by
  unfold friableExponentDirichletExp
  have hfun :
      (fun z : ℂ => P.sum fun m c => c * Complex.exp (-(z * (Real.log (primeProduct m : ℝ) : ℂ)))) =
        (∑ m ∈ P.support,
          fun z : ℂ => P m * Complex.exp (-(z * (Real.log (primeProduct m : ℝ) : ℂ)))) := by
    funext z
    rw [Finsupp.sum]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [iteratedDeriv_sum]
  · rw [Finsupp.sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [iteratedDeriv_const_mul]
    · rw [iteratedDeriv_nat_dirichlet_at_one T (primeProduct m) (primeProduct_pos m).ne']
      have hlogC :
          ((Real.log (primeProduct m : ℝ) : ℂ)) =
            m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ) := by
        rw [log_primeProduct m]
        exact complex_cast_logPrime_sum m
      rw [hlogC]
      ring
    · exact contDiff_exp_neg_mul_log T (Real.log (primeProduct m : ℝ) : ℂ) 1
  · intro m hm
    have hc : ContDiffAt ℂ (T : WithTop ℕ∞) (fun _z : ℂ => P m) 1 := contDiffAt_const
    exact hc.mul (contDiff_exp_neg_mul_log T (Real.log (primeProduct m : ℝ) : ℂ) 1)

/-- The derivative-at-one identity with the prime-log power expanded into explicit
degree-`T` word monomials. This is the formal algebraic step after
`iteratedDeriv_friableExponentDirichletExp_at_one` and before collecting equal
words into multinomial coefficient vectors. -/
theorem iteratedDeriv_friableExponentDirichletExp_at_one_wordExpansion
    (T : ℕ) (P : (Nat.Primes →₀ ℕ) →₀ ℂ) :
    iteratedDeriv T (fun z : ℂ => friableExponentDirichletExp P z) 1 =
      (-1 : ℂ) ^ T * P.sum (fun m c =>
        c * (∑ w ∈ Fintype.piFinset (fun _ : Fin T => m.support),
          ∏ i : Fin T, ((m (w i) : ℂ) * (Real.log (w i : ℕ) : ℂ))) *
          ((primeProduct m : ℂ)⁻¹)) := by
  rw [iteratedDeriv_friableExponentDirichletExp_at_one]
  congr 1
  apply Finsupp.sum_congr
  intro m _hm
  rw [primeLogDot_pow_wordExpansion m T]

end

end GaloisForLFunctions
