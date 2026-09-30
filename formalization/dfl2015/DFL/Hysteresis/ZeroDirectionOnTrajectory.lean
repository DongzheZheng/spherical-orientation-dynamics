import DFL.Hysteresis.OriginalTrajectory

/-!
The zero-direction sign is evaluated on the *original* spherical-mean
elasticity difference, using `original_H_ode`. This does not by itself prove
existence or uniqueness of a zero of that original trajectory.
-/

namespace DFL.Hysteresis.ZeroDirectionOnTrajectory

open DFL.Hysteresis.ZeroDirectionODE
open DFL.Hysteresis.OriginalTrajectory

theorem original_H_deriv_at_zero (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hzero : H n r = 0) :
    deriv (H n) r = F n r 0 := by
  rw [original_H_ode n hn hr, hzero]

/-- Every zero of the original elasticity difference below the threshold
points downward; every zero above it points upward. The threshold is the
unique zero of the exact scalar field `F(r,0)`. -/
theorem exists_original_H_zero_direction (n : ℕ) (hn : 2 ≤ n) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ r : ℝ, 0 < r → r < r₀ → H n r = 0 → deriv (H n) r < 0) ∧
      (∀ r : ℝ, r₀ < r → H n r = 0 → 0 < deriv (H n) r) := by
  obtain ⟨r₀, hr₀, hleft, _, hright⟩ := exists_zero_direction n hn
  refine ⟨r₀, hr₀, ?_, ?_⟩
  · intro r hr hlt hzero
    rw [original_H_deriv_at_zero n hn hr hzero]
    exact hleft r hr hlt
  · intro r hgt hzero
    have hr : 0 < r := by linarith
    rw [original_H_deriv_at_zero n hn hr hzero]
    exact hright r hgt

end DFL.Hysteresis.ZeroDirectionOnTrajectory
