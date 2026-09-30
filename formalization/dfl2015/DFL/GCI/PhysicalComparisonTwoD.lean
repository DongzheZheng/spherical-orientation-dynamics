import DFL.GCI.ComparisonTwoD
import DFL.Geometry.PhysicalSphereTwo

/-!
# Two-dimensional GCI comparison against the actual physical circle mean

The GCI coefficient is defined by the original angular weak equation.
The orientation mean on the right is defined independently from the
original `volume.toSphere` circle measure. The proven complete circle
coordinate law identifies it with the marginal formula in the comparison.
-/

namespace DFL.GCI

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

theorem weak_solution_GCI_lt_physical_circle_mean
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    0 < originalGCICoefficient 2 r s ∧
      originalGCICoefficient 2 r s <
        DFL.Geometry.sphereOrientationMean 2 two_pos r := by
  have h := weak_solution_GCI_comparison_twoD r hr s hs
  rw [DFL.Geometry.sphereOrientationMean_eq_of_moment_bridge
    2 (by decide) DFL.Geometry.sphereMomentBridge_two]
  exact h

theorem original_GCI_twoD_physical_circle_comparison
    (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution 2 r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution 2 r v →
        originalGCICoefficient 2 r v = originalGCICoefficient 2 r s) ∧
      0 < originalGCIDenominator 2 r s ∧
      0 < originalGCICoefficient 2 r s ∧
      originalGCICoefficient 2 r s <
        DFL.Geometry.sphereOrientationMean 2 two_pos r := by
  obtain ⟨s, hs, huniq, hD, hpos, hlt⟩ :=
    original_GCI_twoD_full_comparison r hr
  refine ⟨s, hs, huniq, hD, hpos, ?_⟩
  rw [DFL.Geometry.sphereOrientationMean_eq_of_moment_bridge
    2 (by decide) DFL.Geometry.sphereMomentBridge_two]
  exact hlt

end

end DFL.GCI
