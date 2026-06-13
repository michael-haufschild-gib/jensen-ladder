/-
JensenLadder — certified hyperbolicity of the Riemann xi Jensen sections.

TARGET THEOREM (statement frozen after numerical pre-certification):
for every 1 ≤ d ≤ D₀, the Jensen section

  J_d(X) = ∑ k in range (d+1), (-1)^k * (d falling k / d^k) * M k / (2k)! * X^k

(with M k the even moments of the classical theta kernel Φ) has d real
positive roots — i.e. is hyperbolic in w (X = w²).

Planned layers:
  * `Moments`     — rational interval enclosures of M k with PROVED error
                    bounds (Taylor-remainder exp bounds; explicit n-series
                    and tail remainders; the u = 0 endpoint as a lemma).
  * `Sections`    — the polynomials J_d over ℚ-interval coefficient boxes.
  * `Sturm`       — root-counting certificates valid over the whole box.
  * `Main`        — the assembled theorem, axiom-clean.

Status: SCAFFOLD. No proofs, no sorries, no claims. Lean work gated on
(G1) statement/division concurrence, (G2) certificate-grade enclosures +
D₀ freeze. See docs/ROADMAP.md.
-/

namespace JensenLadder

end JensenLadder
