import DFL.GCI.AngularMomentGeneral
import DFL.GCI.ComparisonGenericUpper

/-!
# Original GCI strict upper comparison in every ambient dimension at least four

No sign assumption on the original weak solution or its numerator is used.
-/

namespace DFL.GCI

noncomputable section

/-- Every original represented weak GCI solution in ambient dimension
`n ≥ 4` obeys the shifted-mean bound. -/
theorem original_GCI_shift_upper_ge_four
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s ≤
      DFL.orientationMean (n + 2) r :=
  weak_solution_coefficient_le_shift_mean_of_moment
    n (by omega) r hr s hs
      (weak_solution_moment_identity_ge_four n hn r s hs)

/-- The original historical strict upper inequality for every original
represented weak GCI solution in dimensions `n ≥ 4`. -/
theorem original_GCI_strict_upper_ge_four
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s < DFL.orientationMean n r :=
  weak_solution_coefficient_lt_orientation_of_moment
    n (by omega) r hr s hs
      (weak_solution_moment_identity_ge_four n hn r s hs)

end

end DFL.GCI
