import Mathlib

/-!
# The Sato–Tate measure moments vanish (analytic core of equidistribution, Tier A)

This file formalizes the **analytic backbone** of the Sato–Tate dictionary
(`automorphic-continent-rankin-selberg-ramanujan.md` §3′), complementing the
algebraic character identity `SatakeSymPower.symPowerGL2_eq_chebyshevS`
(`Symᵏ a_p = U_k(cos θ_p)`): the **moments of the Sato–Tate measure
`μ_ST = (2/π) sin²θ dθ` against the symmetric-power characters `U_k` vanish**,

  `∫₀^π U_k(cos θ) · (2/π) sin²θ dθ = δ_{k,0}`.

For `k ≥ 1` this says the average of `Symᵏ a_p` against `μ_ST` is `0` — the
orthogonality that *drives* Sato–Tate equidistribution (the Weyl/moment criterion:
all higher `U_k`-moments vanish ⟺ the angles equidistribute w.r.t. `μ_ST`).

The proof is the classical trig orthogonality: `U_k(cos θ) sin θ = sin((k+1)θ)`
(`Polynomial.Chebyshev.U_real_cos`), product-to-sum
`sin((k+1)θ) sin θ = ½(cos kθ − cos(k+2)θ)`, and `∫₀^π cos(jθ) dθ = π·δ_{j,0}`.

This is the moment-vanishing of the Sato–Tate measure only. It is **not** the
Sato–Tate equidistribution theorem itself (the input is the analytic continuation /
non-vanishing of `Symᵏ L(s,π)`, BLGHT, which provides the prime-side average
equal to this integral); we formalize the measure-side moments, the target the
prime averages converge to.
-/

open intervalIntegral Real
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **`∫₀^π cos(jθ) dθ = π·δ_{j,0}`.** The basic cosine orthogonality integral over
`[0, π]` for an integer frequency `j` — `π` when `j = 0`, else `0` (since
`sin(jπ) = 0`). The atom underlying the Sato–Tate moment vanishing. -/
theorem integral_cos_nat_mul (j : ℕ) :
    ∫ θ in (0:ℝ)..Real.pi, Real.cos ((j : ℝ) * θ) = if j = 0 then Real.pi else 0 := by
  rcases eq_or_ne j 0 with hj | hj
  · subst hj; simp
  · rw [if_neg hj]
    have hjr : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hjr, mul_zero,
      integral_cos, Real.sin_nat_mul_pi]
    simp

/-- **Trig orthogonality `∫₀^π sin((k+1)θ) sin θ dθ = (π/2)·δ_{k,0}`.** The Fourier
orthogonality of `sin((k+1)θ)` and `sin θ` over `[0, π]`, via product-to-sum and
`integral_cos_nat_mul`. This is the orthogonality that makes the Sato–Tate moments
vanish for `k ≥ 1`. -/
theorem integral_sin_succ_mul_sin (k : ℕ) :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin (((k : ℝ) + 1) * θ) * Real.sin θ
      = if k = 0 then Real.pi / 2 else 0 := by
  have hpt : ∀ θ : ℝ, Real.sin (((k : ℝ) + 1) * θ) * Real.sin θ
      = (Real.cos ((k : ℝ) * θ) - Real.cos (((k : ℝ) + 2) * θ)) / 2 := by
    intro θ
    have h1 : Real.cos ((k : ℝ) * θ) = Real.cos (((k : ℝ) + 1) * θ - θ) := by ring_nf
    have h2 : Real.cos (((k : ℝ) + 2) * θ) = Real.cos (((k : ℝ) + 1) * θ + θ) := by ring_nf
    rw [h1, h2, Real.cos_sub, Real.cos_add]; ring
  rw [intervalIntegral.integral_congr
        (g := fun θ => (Real.cos ((k : ℝ) * θ) - Real.cos (((k : ℝ) + 2) * θ)) / 2)
        (fun θ _ => hpt θ),
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun θ => Real.cos ((k : ℝ) * θ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ => Real.cos (((k : ℝ) + 2) * θ)).intervalIntegrable _ _)]
  rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) from by push_cast; ring,
    integral_cos_nat_mul k, integral_cos_nat_mul (k + 2)]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; norm_num
  · simp only [if_neg hk, if_neg (show k + 2 ≠ 0 from by omega)]; norm_num

/-- **The Sato–Tate moments vanish: `∫₀^π U_k(cos θ) (2/π) sin²θ dθ = δ_{k,0}`.**
The `k`-th moment of the Sato–Tate measure `μ_ST = (2/π) sin²θ dθ` against the
symmetric-power character `U_k(cos θ)` (`= Symᵏ a_p`, via
`SatakeSymPower.symPowerGL2_eq_chebyshevS`). For `k ≥ 1` it is `0`: `Symᵏ` averages
to zero against `μ_ST` — the orthogonality (Weyl-criterion input) that drives
Sato–Tate equidistribution. Proved from `integral_sin_succ_mul_sin` via
`U_k(cos θ) sin θ = sin((k+1)θ)`. The measure-side moment only; the prime-side
average (BLGHT) that converges to it is not formalized. -/
theorem satoTate_moment (k : ℕ) :
    ∫ θ in (0:ℝ)..Real.pi,
        (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * (2 / Real.pi * Real.sin θ ^ 2)
      = if k = 0 then 1 else 0 := by
  have hpt : ∀ θ : ℝ,
      (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * (2 / Real.pi * Real.sin θ ^ 2)
        = (2 / Real.pi) * (Real.sin (((k : ℝ) + 1) * θ) * Real.sin θ) := by
    intro θ
    have hU := Polynomial.Chebyshev.U_real_cos θ (k : ℤ)
    rw [sq, show (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ)
              * (2 / Real.pi * (Real.sin θ * Real.sin θ))
          = (2 / Real.pi)
              * (((Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * Real.sin θ) * Real.sin θ)
          from by ring, hU]
    push_cast; ring_nf
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul,
    integral_sin_succ_mul_sin]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp
  · rw [if_neg hk, if_neg hk]; ring

/-- **Real cosine integral `∫₀^π cos(cθ) dθ = sin(cπ)/c`** for `c ≠ 0.** The
real-frequency form (the `c = j ≠ 0` case recovers `integral_cos_nat_mul`); the
engine of the full orthogonality below. -/
theorem integral_cos_mul_pi (c : ℝ) (hc : c ≠ 0) :
    ∫ θ in (0:ℝ)..Real.pi, Real.cos (c * θ) = Real.sin (c * Real.pi) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, mul_zero, integral_cos]
  simp [div_eq_inv_mul]

/-- **Full Fourier orthogonality `∫₀^π sin(mθ) sin(nθ) dθ = (π/2)·δ_{m,n}`** for
`m, n ≥ 1.** The complete orthogonality of the sine system on `[0, π]`
(`integral_sin_succ_mul_sin` is the `n = 1` case). Via product-to-sum and
`integral_cos_mul_pi`, using `sin(jπ) = 0` for integer `j` (both `m+n` and the
nonzero integer `m−n`). -/
theorem integral_sin_mul_sin (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin ((m:ℝ) * θ) * Real.sin ((n:ℝ) * θ)
      = if m = n then Real.pi / 2 else 0 := by
  have hpt : ∀ θ : ℝ, Real.sin ((m:ℝ) * θ) * Real.sin ((n:ℝ) * θ)
      = (Real.cos (((m:ℝ) - n) * θ) - Real.cos (((m:ℝ) + n) * θ)) / 2 := by
    intro θ
    have h1 : Real.cos (((m:ℝ) - n) * θ) = Real.cos ((m:ℝ) * θ - (n:ℝ) * θ) := by ring_nf
    have h2 : Real.cos (((m:ℝ) + n) * θ) = Real.cos ((m:ℝ) * θ + (n:ℝ) * θ) := by ring_nf
    rw [h1, h2, Real.cos_sub, Real.cos_add]; ring
  rw [intervalIntegral.integral_congr
        (g := fun θ => (Real.cos (((m:ℝ) - n) * θ) - Real.cos (((m:ℝ) + n) * θ)) / 2)
        (fun θ _ => hpt θ), intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun θ => Real.cos (((m:ℝ) - n) * θ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ => Real.cos (((m:ℝ) + n) * θ)).intervalIntegrable _ _)]
  have hsum : ∫ θ in (0:ℝ)..Real.pi, Real.cos (((m:ℝ) + n) * θ) = 0 := by
    rw [integral_cos_mul_pi _ (by positivity),
      show ((m:ℝ) + n) = ((m + n : ℕ):ℝ) from by push_cast; ring, Real.sin_nat_mul_pi]; simp
  rcases eq_or_ne m n with hmn | hmn
  · subst hmn; rw [if_pos rfl, hsum, sub_zero, show ((m:ℝ) - m) = 0 from by ring]; simp
  · rw [if_neg hmn, hsum, sub_zero]
    have hdiff : ((m:ℝ) - n) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hmn
    rw [integral_cos_mul_pi _ hdiff,
      show ((m:ℝ) - n) = (((m:ℤ) - n : ℤ):ℝ) from by push_cast; ring, Real.sin_int_mul_pi]; simp

/-- **The `U_k` are orthonormal for the Sato–Tate measure:
`∫₀^π U_j(cos θ) U_k(cos θ) (2/π) sin²θ dθ = δ_{j,k}`.** The symmetric-power
characters `U_k(cos θ) = Symᵏ a_p` are the **orthogonal polynomials of the
Sato–Tate measure** `μ_ST = (2/π) sin²θ dθ` — the spectral basis of `L²(μ_ST)`
underlying the moment/Weyl criterion for equidistribution. Generalizes
`satoTate_moment` (the `j = 0`, `U_0 = 1` case). Via `U_real_cos`
(`U_k(cos θ) sin θ = sin((k+1)θ)`) reducing to `integral_sin_mul_sin`. -/
theorem satoTate_orthonormal (j k : ℕ) :
    ∫ θ in (0:ℝ)..Real.pi,
        (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)
          * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * (2 / Real.pi * Real.sin θ ^ 2)
      = if j = k then 1 else 0 := by
  have hpt : ∀ θ : ℝ,
      (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)
          * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * (2 / Real.pi * Real.sin θ ^ 2)
        = (2 / Real.pi) * (Real.sin (((j + 1 : ℕ) : ℝ) * θ) * Real.sin (((k + 1 : ℕ) : ℝ) * θ)) := by
    intro θ
    have hUj := Polynomial.Chebyshev.U_real_cos θ (j : ℤ)
    have hUk := Polynomial.Chebyshev.U_real_cos θ (k : ℤ)
    rw [sq, show (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)
              * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ)
              * (2 / Real.pi * (Real.sin θ * Real.sin θ))
          = (2 / Real.pi) * (((Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) * Real.sin θ)
              * ((Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) * Real.sin θ)) from by ring,
      hUj, hUk]
    push_cast; ring_nf
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul,
    integral_sin_mul_sin (j + 1) (k + 1) (by omega) (by omega)]
  rcases eq_or_ne j k with hjk | hjk
  · subst hjk; simp
  · rw [if_neg (by omega : j + 1 ≠ k + 1), if_neg hjk]; ring

end

end GaloisForLFunctions
