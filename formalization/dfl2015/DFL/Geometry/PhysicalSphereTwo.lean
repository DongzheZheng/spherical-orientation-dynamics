import DFL.Geometry.CircleLawFull
import DFL.Geometry.MomentBridgeTwo
import DFL.Hysteresis.NondegenerateFold

/-!
# The original unit-circle case of the DFL 2015 single-valley conjecture

The surface measure here is the actual `volume.toSphere` measure on the
unit circle.  Its complete first-coordinate pushforward is identified
with the arcsine measure, including the singular endpoints.  The
resulting moment identities feed the already proved all-dimensional
single-valley theorem.
-/

namespace DFL.Geometry

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

/-- The original circle's geometric moments equal the original DFL
one-dimensional moments, with the common surface factor `2`. -/
theorem sphereMomentBridge_two : SphereMomentBridge 2 two_pos :=
  sphereMomentBridge_two_of_coordinateLaw
    coordinateLaw_two_eq_two_smul_measureT

/-- The actual unit-circle equilibrium density has a unique valley,
including uniqueness of the critical point. -/
theorem sphere_isUnimodal_two : SphereIsUnimodal 2 two_pos :=
  sphere_isUnimodal_two_of_coordinateLaw
    coordinateLaw_two_eq_two_smul_measureT

/-- The physical unit-circle density has one nondegenerate fold, with
strictly negative slope before it and strictly positive slope after it. -/
theorem sphere_nondegenerateFold_two :
    ∃ rStar : ℝ,
      0 < rStar ∧
      (∀ r : ℝ, 0 < r → r < rStar →
        deriv (sphereEquilibriumDensity 2 two_pos) r < 0) ∧
      deriv (sphereEquilibriumDensity 2 two_pos) rStar = 0 ∧
      (∀ r : ℝ, rStar < r →
        0 < deriv (sphereEquilibriumDensity 2 two_pos) r) ∧
      0 < deriv (deriv (sphereEquilibriumDensity 2 two_pos)) rStar := by
  have heq := sphereEquilibriumDensity_eq_of_moment_bridge 2 (by decide)
    sphereMomentBridge_two
  simpa only [heq, DFL.NondegenerateFold] using
    (DFL.Hysteresis.original_nondegenerateFold 2 (by decide))

end

end DFL.Geometry
