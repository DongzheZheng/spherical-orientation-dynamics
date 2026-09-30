import DFL.Hysteresis.ZeroDirection
import DFL.Hysteresis.PositiveRoot

/-!
# Exact scaling bridge between the two zero-direction calculations

The manuscript has `z/r = u(χ)` and `m/r = v(χ)`.  Under these identities,
the positive-root threshold ratio is the reciprocal of the rational product
`q(χ) = u(χ)(u(χ)+v(χ))`.  The identities `z/r = u`, `m/r = v` themselves
still need a Lean derivation from the actual ODE coefficients.
-/

namespace DFL.Hysteresis.ZeroDirectionBridge

open DFL.Hysteresis.ZeroDirection
open DFL.Hysteresis.PositiveRoot

theorem thresholdRatio_scaled (n : ℕ) (hn : 2 ≤ n) (χ r : ℝ)
    (hχ : 1 < χ) (hr : 0 < r) :
    thresholdRatio r (r * u n χ) (r * v n χ) = 1 / q n χ := by
  have hu : 0 < u n χ := u_pos n hn hχ
  have hv : 0 < v n χ := v_pos n hn hχ
  have hsum : 0 < u n χ + v n χ := by linarith
  have hq : 0 < q n χ := mul_pos hu hsum
  unfold thresholdRatio q
  field_simp [ne_of_gt hr, ne_of_gt hu, ne_of_gt hsum]

end DFL.Hysteresis.ZeroDirectionBridge
