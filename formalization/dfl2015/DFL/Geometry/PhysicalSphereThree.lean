import DFL.Geometry.LawThreeFull
import DFL.Geometry.MomentBridgeThree
import DFL.Hysteresis.NondegenerateFold

/-!
# The original physical two-sphere single-valley theorem

All objects here live on the actual unit sphere in `ℝ³`, equipped with the
cone-induced area measure from ambient Euclidean volume.  The coordinate-law
input is proved geometrically in `LawThreeFull`, not postulated here.
-/

namespace DFL.Geometry

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

/-- Unconditional common-constant moment identity for the physical `S²`. -/
theorem sphereMomentBridge_three : SphereMomentBridge 3 three_pos :=
  sphereMomentBridge_three_of_coordinateLaw coordinateLaw_three_eq_smul_volume

/-- The DFL 2015 single-valley conjecture on the original, physical `S²`
measure, with its actual field partition and first moment. -/
theorem sphere_isUnimodal_three : SphereIsUnimodal 3 three_pos :=
  sphere_isUnimodal_of_moment_bridge 3 (by decide) sphereMomentBridge_three

/-- The physical two-sphere curve also has exactly one nondegenerate fold,
with a strictly negative slope before and positive slope after it. -/
theorem sphere_nondegenerateFold_three :
    ∃ rStar : ℝ,
      0 < rStar ∧
      (∀ r : ℝ, 0 < r → r < rStar →
        deriv (sphereEquilibriumDensity 3 three_pos) r < 0) ∧
      deriv (sphereEquilibriumDensity 3 three_pos) rStar = 0 ∧
      (∀ r : ℝ, rStar < r →
        0 < deriv (sphereEquilibriumDensity 3 three_pos) r) ∧
      0 < deriv (deriv (sphereEquilibriumDensity 3 three_pos)) rStar := by
  have heq := sphereEquilibriumDensity_eq_of_moment_bridge 3 (by decide)
    sphereMomentBridge_three
  simpa only [heq, DFL.NondegenerateFold] using
    (DFL.Hysteresis.original_nondegenerateFold 3 (by decide))

end

end DFL.Geometry
