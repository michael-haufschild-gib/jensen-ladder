import JensenLadder.RvMXiEntire
import JensenLadder.HurwitzRealRootedLimit

/-!
# Coordinate link: the s-variable `xiE` is the z-variable `xiEntire`

`RvMXiEntire.xiE` (in the natural `s`-variable, `s = ½ + iz`) and the existing
`HurwitzBridge.xiEntire` (in the `z`-variable) are the *same* entire ξ in different coordinates.
This identity transfers the z-variable infrastructure already proved for `xiEntire`
(growth/order bounds, the Jensen divisor-count `XiZeroCounting.xiEntire_divisor_count_le` giving
`n(r) = O(r log r)`) onto `xiE`, en route to the Riemann–von Mangoldt count.

RH-agnostic. Does not prove RH.
-/

namespace JensenLadder.RvMXiEntire

open Complex

/-- The s-variable entire ξ equals the z-variable `HurwitzBridge.xiEntire` under `s = ½ + i z`. -/
theorem xiE_eq_hurwitz (z : ℂ) : xiE (1 / 2 + Complex.I * z) = HurwitzBridge.xiEntire z := by
  unfold xiE HurwitzBridge.xiEntire
  ring

end JensenLadder.RvMXiEntire
