import DFL.GCI.AngularShiftMoment2D
import DFL.GCI.PositiveTwoD
import DFL.Hysteresis.DimensionShift

/-!
# The original 2015 GCI comparison in ambient dimension two

This theorem uses the original angular weak solution and the original
coefficient integrals.  The upper bound follows from the weak energy
comparison with the physical sine test, the exact marginal change of
variables, and strict ordering of the dimension-four and dimension-two
orientation means.
-/

namespace DFL.GCI

noncomputable section

/-- Every represented original weak solution in ambient dimension two
satisfies the full strict 2015 coefficient comparison. -/
theorem weak_solution_GCI_comparison_twoD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    0 < originalGCICoefficient 2 r s ∧
      originalGCICoefficient 2 r s < DFL.orientationMean 2 r := by
  refine ⟨weak_solution_coefficient_pos_twoD r hr s hs, ?_⟩
  have hle : originalGCICoefficient 2 r s ≤
      DFL.orientationMean 4 r := by
    rw [orientationMean_four_eq_twoD_shift_ratio]
    exact weak_solution_coefficient_le_shift_moment_twoD r hr s hs
  have hshift : DFL.orientationMean 4 r <
      DFL.orientationMean 2 r := by
    simpa using
      (DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
        2 (by omega) hr)
  exact lt_of_le_of_lt hle hshift

/-- Existence, coefficient uniqueness, positive denominator, and the
strict historical GCI inequality, for every `r>0` in ambient dimension
two.  The unrestricted `n≥2` target remains separate. -/
theorem original_GCI_twoD_full_comparison
    (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution 2 r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution 2 r v →
        originalGCICoefficient 2 r v = originalGCICoefficient 2 r s) ∧
      0 < originalGCIDenominator 2 r s ∧
      0 < originalGCICoefficient 2 r s ∧
      originalGCICoefficient 2 r s < DFL.orientationMean 2 r := by
  obtain ⟨s, hs, huniq, hD, hpositive⟩ :=
    original_GCI_twoD_exists_unique_positive r hr
  exact ⟨s, hs, huniq, hD, hpositive,
    (weak_solution_GCI_comparison_twoD r hr s hs).2⟩

end

end DFL.GCI
