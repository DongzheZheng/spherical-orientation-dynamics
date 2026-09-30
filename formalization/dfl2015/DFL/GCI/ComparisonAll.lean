import DFL.GCI.OriginalExistenceAll
import DFL.GCI.AngularSpectralAll
import DFL.GCI.ComparisonTwoD
import DFL.GCI.CoefficientUniquenessAll
import DFL.GCI.OriginalUniquenessAll
import DFL.GCI.StrictShiftAll
import DFL.GCI.StrictShiftTwoD
import DFL.Geometry.PhysicalSphereAll

/-!
# Full represented original GCI comparison in every dimension

This assembles existence for the actual angular source, coefficient
uniqueness, and both strict coefficient signs. The theorem has the exact
type `DFL2015GCIComparison`; no weak-solution or spectral premise remains.
The target uses the absolutely continuous representative realization of
the original weighted Dirichlet space. ClassicalEnergyDomainBridge proves
its identification with the conventional smooth Dirichlet graph completion;
ClassicalComparisonAll packages that domain and this comparison together.
-/

namespace DFL.GCI

noncomputable section

theorem original_GCI_positive_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCICoefficient n r s := by
  by_cases htwo : n = 2
  · subst n
    exact weak_solution_coefficient_pos_twoD r hr s hs
  · exact original_GCI_positive_ge_three n (by omega) r hr s hs

/-- Function-level uniqueness in the original open physical interval,
including the separately represented circular case. -/
theorem weak_solution_g_unique_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (s t : AngularState)
    (hs : OriginalWeakGCISolution n r s) (ht : OriginalWeakGCISolution n r t)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) : s.g θ = t.g θ := by
  by_cases htwo : n = 2
  · subst n
    exact weak_solution_g_unique_twoD r hr s t hs ht θ ⟨hθ.1.le, hθ.2.le⟩
  · exact weak_solution_g_unique_ge_three n (by omega) r s t hs ht θ hθ

theorem weak_solution_coefficient_lt_shift_mean_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s < DFL.orientationMean (n + 2) r := by
  by_cases htwo : n = 2
  · subst n
    exact weak_solution_coefficient_lt_shift_mean_twoD r hr s hs
  · exact weak_solution_coefficient_lt_shift_mean_ge_three n (by omega) r hr s hs

/-- The manuscript's stronger strict chain, with an actual original
weak solution and coefficient uniqueness in every historical dimension. -/
theorem original_GCI_all_strict_shift_chain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution n r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution n r v →
        originalGCICoefficient n r v = originalGCICoefficient n r s) ∧
      0 < originalGCIDenominator n r s ∧
      0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s < DFL.orientationMean (n + 2) r ∧
      DFL.orientationMean (n + 2) r < DFL.orientationMean n r := by
  obtain ⟨s, hs⟩ := original_weak_GCI_exists_all n hn r hr
  exact ⟨s, hs,
    fun v hv => weak_solution_coefficient_unique_all n hn r hr v s hv hs,
    weak_solution_denominator_pos n hn r s hs,
    original_GCI_positive_all n hn r hr s hs,
    weak_solution_coefficient_lt_shift_mean_all n hn r hr s hs,
    DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift n hn hr⟩

/-- The entire represented angular Conjecture 5.1 package, for all
ambient dimensions and every positive field. -/
theorem dfl2015_gci_comparison : DFL2015GCIComparison := by
  intro n hn r hr
  obtain ⟨s, hs⟩ := original_weak_GCI_exists_all n hn r hr
  exact ⟨s, hs,
    fun v hv => weak_solution_coefficient_unique_all n hn r hr v s hv hs,
    weak_solution_denominator_pos n hn r s hs,
    original_GCI_positive_all n hn r hr s hs,
    original_GCI_strict_upper_all n hn r hr s hs⟩

/-- Direct comparison with the equilibrium mean of the genuine physical
sphere measure, using its already proved coordinate law. -/
theorem original_GCI_all_physical_sphere_comparison
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution n r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution n r v →
        originalGCICoefficient n r v = originalGCICoefficient n r s) ∧
      0 < originalGCIDenominator n r s ∧
      0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s <
        DFL.Geometry.sphereOrientationMean n (by omega) r := by
  obtain ⟨s, hs, huniq, hD, hpos, hlt⟩ := dfl2015_gci_comparison n hn r hr
  refine ⟨s, hs, huniq, hD, hpos, ?_⟩
  rw [DFL.Geometry.sphereOrientationMean_eq_of_moment_bridge n hn
    (DFL.Geometry.sphereMomentBridge_all n hn)]
  exact hlt

end
end DFL.GCI
