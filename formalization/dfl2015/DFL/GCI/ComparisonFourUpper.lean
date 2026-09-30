import DFL.GCI.AngularShiftMoment
import DFL.GCI.AngularMoment4D
import DFL.Hysteresis.DimensionShift

/-!
# Original GCI upper comparison in ambient dimension four

The original weak-solution moment identity, forcing-energy Cauchy
inequality, and exact marginal dimension shift give the strict historical
upper bound in dimension four.  Positivity of the dimension-four GCI
numerator is a separate source-level problem.
-/

namespace DFL.GCI

noncomputable section

/-- The original dimension-four coefficient is bounded by the exact
dimension-six orientation mean for every original weak solution. -/
theorem weak_solution_coefficient_le_shift_mean_fourD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 4 r s) :
    originalGCICoefficient 4 r s ≤ DFL.orientationMean 6 r := by
  have hD := weak_solution_denominator_pos 4 (by omega) r s hs
  have hZ := originalForcingNorm_pos_of_weak_solution
    4 (by omega) r s hs
  have hC := weak_solution_forcing_energy_cauchy 4 (by omega) r s hs
  have hT := sineTest_self_energy_eq_forcing_add_shift
    4 (by omega) r
  have hM := weak_solution_moment_identity_fourD r s hs
  have hND : originalForcingNorm 4 r *
      originalGCINumerator 4 r s ≤
      originalGCIDenominator 4 r s * originalShiftMoment 4 r := by
    norm_num at hT
    nlinarith [mul_nonneg hr.le hZ.le]
  rw [orientationMean_shift_eq_angular_shift_ratio 4 (by omega) r]
  unfold originalGCICoefficient
  exact (div_le_div_iff₀ hD hZ).2 (by nlinarith [hND])

/-- The strict original upper comparison in dimension four follows
because the original orientation mean strictly falls from dimension
four to six at every positive concentration. -/
theorem weak_solution_coefficient_lt_orientation_fourD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 4 r s) :
    originalGCICoefficient 4 r s < DFL.orientationMean 4 r := by
  have hle := weak_solution_coefficient_le_shift_mean_fourD r hr s hs
  have hshift : DFL.orientationMean 6 r <
      DFL.orientationMean 4 r := by
    simpa using
      (DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
        4 (by omega) hr)
  exact lt_of_le_of_lt hle hshift

end

end DFL.GCI
