import Mathlib.Tactic

/-!
# Hodge signature baby carrier

This module records a rank-two unconditional baby instance of the signature
phrasing from the carrier prompt.

The form is the coordinate Lorentzian/Hodge block

```text
B((a,b),(c,d)) = H*a*c - N*b*d,
```

with ample direction `h = (1,0)`.  If `H > 0` and `N >= 0`, then `h` has
positive self-pairing and the `B`-orthogonal complement of `h` is nonpositive.
The associated Cauchy-Schwarz/Castelnuovo defect is explicitly `H*N*b^2`.

This does not construct the global arithmetic carrier or prove RH.  It is a
formal baby signature block: the requested `(1, dim-1)` mechanism is present in
the smallest coordinate model, with no hypothesis about zeta zeros.

Evidence class: formal/certificate artifact; proved lemma.  Theorem M is
proven, but Theorem M does not prove RH by itself.
-/

namespace JensenLadder
namespace HodgeSignatureBabyCarrier

/-- Rank-two Hodge/Lorentzian bilinear form in coordinates. -/
def form (H N : ℝ) (a b c d : ℝ) : ℝ :=
  H * a * c - N * b * d

/-- Self-pairing for the rank-two Hodge block. -/
def self (H N a b : ℝ) : ℝ :=
  form H N a b a b

/-- Self-pairing of the ample direction `(1,0)`. -/
def ampleSelf (H N : ℝ) : ℝ :=
  form H N 1 0 1 0

/-- Pairing with the ample direction `(1,0)`. -/
def pairWithAmple (H N a b : ℝ) : ℝ :=
  form H N a b 1 0

/-- The rank-two Hodge/Cauchy-Schwarz defect against the ample direction. -/
def defect (H N a b : ℝ) : ℝ :=
  pairWithAmple H N a b ^ 2 - self H N a b * ampleSelf H N

/-- The ample direction has self-pairing `H`. -/
theorem ampleSelf_eq (H N : ℝ) :
    ampleSelf H N = H := by
  unfold ampleSelf form
  ring

/-- `H > 0` makes the ample direction positive. -/
theorem ampleSelf_pos {H N : ℝ}
    (hH : 0 < H) :
    0 < ampleSelf H N := by
  rw [ampleSelf_eq]
  exact hH

/-- Orthogonality to the ample direction forces the first coordinate to vanish. -/
theorem first_coord_eq_zero_of_pairWithAmple_eq_zero
    {H N a b : ℝ}
    (hH : 0 < H)
    (horth : pairWithAmple H N a b = 0) :
    a = 0 := by
  unfold pairWithAmple form at horth
  nlinarith

/-- Once the first coordinate vanishes, the self-pairing is nonpositive. -/
theorem self_nonpositive_of_first_coord_zero
    {H N a b : ℝ}
    (hN : 0 <= N)
    (ha : a = 0) :
    self H N a b <= 0 := by
  unfold self form
  rw [ha]
  nlinarith [sq_nonneg b]

/--
The primitive hyperplane `h^perp` is nonpositive.

This is the rank-two baby instance of `(★)`: for vectors orthogonal to the
ample direction, the form is `<= 0`.
-/
theorem primitive_self_nonpositive
    {H N a b : ℝ}
    (hH : 0 < H)
    (hN : 0 <= N)
    (horth : pairWithAmple H N a b = 0) :
    self H N a b <= 0 := by
  exact self_nonpositive_of_first_coord_zero hN
    (first_coord_eq_zero_of_pairWithAmple_eq_zero hH horth)

/-- The Hodge/Cauchy-Schwarz defect is exactly `H*N*b^2`. -/
theorem defect_eq (H N a b : ℝ) :
    defect H N a b = H * N * b ^ 2 := by
  unfold defect pairWithAmple self ampleSelf form
  ring

/-- The Hodge/Cauchy-Schwarz defect is nonnegative when `H,N >= 0`. -/
theorem defect_nonnegative
    {H N a b : ℝ}
    (hH : 0 <= H)
    (hN : 0 <= N) :
    0 <= defect H N a b := by
  rw [defect_eq]
  positivity

/-- Strict primitive negativity away from zero when `N > 0`. -/
theorem primitive_self_negative_of_second_coord_ne_zero
    {H N b : ℝ}
    (hN : 0 < N)
    (hb : b ≠ 0) :
    self H N 0 b < 0 := by
  unfold self form
  nlinarith [sq_pos_of_ne_zero hb]

end HodgeSignatureBabyCarrier
end JensenLadder
