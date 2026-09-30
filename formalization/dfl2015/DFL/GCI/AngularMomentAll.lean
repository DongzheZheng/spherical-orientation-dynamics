import DFL.GCI.AngularMomentThreeBridge
import DFL.GCI.SqrtSinFlux
import DFL.GCI.AngularMoment2D
import DFL.GCI.ComparisonGenericUpper

/-!
# Exact original weak moment and strict upper coefficient bound in every dimension

The dimension-three endpoint flux is handled by its proved absolute
continuity.  The result is quantified over the actual represented original
angular energy space and weak equation; it does not establish existence,
positive numerator, or the paper's full conjecture in dimensions above two.
-/

namespace DFL.GCI

noncomputable section

theorem weak_solution_moment_identity_three
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s) :
    originalForcingNorm 3 r =
      2 * originalGCIDenominator 3 r s +
        r * originalGCINumerator 3 r s := by
  have hFluxAC : AbsolutelyContinuousOnInterval
      (momentFlux 3 r) (0 : ℝ) Real.pi :=
    momentFlux_three_AC r
  exact weak_solution_moment_identity_three_of_flux_AC r s hs hFluxAC

/-- Exact source moment for every original represented weak solution and
every original ambient dimension `n ≥ 2`. -/
theorem weak_solution_moment_identity_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    originalForcingNorm n r =
      ((n : ℝ) - 1) * originalGCIDenominator n r s +
        r * originalGCINumerator n r s := by
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h2 | h3 | h4
  · subst n
    norm_num
    exact weak_solution_moment_identity_twoD r s hs
  · subst n
    norm_num
    exact weak_solution_moment_identity_three r s hs
  · exact weak_solution_moment_identity_ge_four n h4 r s hs

/-- The exact original weak moment and energy Cauchy bound yield the
dimension-shifted orientation-mean upper bound in all `n ≥ 2`. -/
theorem original_GCI_shift_upper_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s ≤ DFL.orientationMean (n + 2) r :=
  weak_solution_coefficient_le_shift_mean_of_moment
    n hn r hr s hs (weak_solution_moment_identity_all n hn r s hs)

/-- The original 2015 strict upper comparison for every represented weak
solution, in every ambient dimension `n ≥ 2` and positive concentration. -/
theorem original_GCI_strict_upper_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s < DFL.orientationMean n r :=
  weak_solution_coefficient_lt_orientation_of_moment
    n hn r hr s hs (weak_solution_moment_identity_all n hn r s hs)

end

end DFL.GCI
