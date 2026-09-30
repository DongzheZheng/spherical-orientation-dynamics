import DFL.GCI.AngularShiftMoment
import DFL.Hysteresis.DimensionShift

/-!
# General upper-comparison mechanism for the original GCI problem

The only additional input is an *exact original weak-solution moment
identity*.  It has been independently proved in ambient dimensions two
and four.  No sign or comparison hypothesis about the coefficient is
assumed here.
-/

namespace DFL.GCI

noncomputable section

/-- The source-level moment identity converts original energy Cauchy
into a bound by the original orientation mean two dimensions higher. -/
theorem weak_solution_coefficient_le_shift_mean_of_moment
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s)
    (hmoment : originalForcingNorm n r =
      ((n : ℝ) - 1) * originalGCIDenominator n r s +
        r * originalGCINumerator n r s) :
    originalGCICoefficient n r s ≤
      DFL.orientationMean (n + 2) r := by
  have hD := weak_solution_denominator_pos n hn r s hs
  have hZ := originalForcingNorm_pos_of_weak_solution n hn r s hs
  have hC := weak_solution_forcing_energy_cauchy n hn r s hs
  have hT := sineTest_self_energy_eq_forcing_add_shift n hn r
  rw [hT] at hC
  have hM : originalForcingNorm n r -
      ((n : ℝ) - 1) * originalGCIDenominator n r s =
        r * originalGCINumerator n r s := by
    linarith [hmoment]
  have hbound :
      originalForcingNorm n r *
        (r * originalGCINumerator n r s) ≤
      originalGCIDenominator n r s *
        (r * originalShiftMoment n r) := by
    calc
      _ = originalForcingNorm n r *
            (originalForcingNorm n r -
              ((n : ℝ) - 1) * originalGCIDenominator n r s) := by
        rw [hM]
      _ = (originalForcingNorm n r) ^ 2 -
            originalGCIDenominator n r s *
              (((n : ℝ) - 1) * originalForcingNorm n r) := by ring
      _ ≤ originalGCIDenominator n r s *
            (r * originalShiftMoment n r) := by nlinarith [hC]
  have hND : originalForcingNorm n r *
      originalGCINumerator n r s ≤
      originalGCIDenominator n r s * originalShiftMoment n r := by
    have hmul : r *
        (originalForcingNorm n r * originalGCINumerator n r s) ≤
        r * (originalGCIDenominator n r s * originalShiftMoment n r) := by
      nlinarith [hbound]
    exact (mul_le_mul_iff_right₀ hr).mp hmul
  rw [orientationMean_shift_eq_angular_shift_ratio n hn r]
  unfold originalGCICoefficient
  exact (div_le_div_iff₀ hD hZ).2 (by nlinarith [hND])

/-- The exact original weak moment identity also implies the strict
historical upper bound, using the independently proved dimension shift
for the original marginal orientation means. -/
theorem weak_solution_coefficient_lt_orientation_of_moment
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s)
    (hmoment : originalForcingNorm n r =
      ((n : ℝ) - 1) * originalGCIDenominator n r s +
        r * originalGCINumerator n r s) :
    originalGCICoefficient n r s < DFL.orientationMean n r := by
  exact lt_of_le_of_lt
    (weak_solution_coefficient_le_shift_mean_of_moment
      n hn r hr s hs hmoment)
    (DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
      n hn hr)

end

end DFL.GCI
