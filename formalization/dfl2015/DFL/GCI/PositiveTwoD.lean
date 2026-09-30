import DFL.GCI.AngularSpectral2D
import DFL.GCI.ExplicitSolution2D

/-!
# Existence, uniqueness, and positive coefficient for the original 2D GCI

The witness is an explicit weak solution of the represented original
angular Dirichlet problem.  Positivity is obtained from the strict Picone
energy estimate for *every* weak solution, and the coefficient is
independent of which weak representative is chosen.
-/

namespace DFL.GCI

noncomputable section

/-- The positive half of the original 2015 GCI comparison, including an
actual source-equation solution and uniqueness of the resulting coefficient,
in ambient dimension two.  The historical upper bound is a separate theorem.
-/
theorem original_GCI_twoD_exists_unique_positive (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution 2 r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution 2 r v →
        originalGCICoefficient 2 r v = originalGCICoefficient 2 r s) ∧
      0 < originalGCIDenominator 2 r s ∧
      0 < originalGCICoefficient 2 r s := by
  let s := explicitState r
  have hs : OriginalWeakGCISolution 2 r s :=
    explicit_original_weak_solution_twoD r hr
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro v hv
    exact weak_solution_coefficient_unique_twoD r hr v s hv hs
  · exact weak_solution_denominator_pos 2 (by omega) r s hs
  · exact weak_solution_coefficient_pos_twoD r hr s hs

end

end DFL.GCI
