import continuation.PhysicalGapZero
import continuation.TransverseFirstMinimumUpper

/-! The exact zero-field value of the same original weighted Rayleigh gap
in every physical sphere dimension, with no transverse direction input. -/
noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLSphere DFLTransverseSphere
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]

/-- The actual physical weighted gap at zero field equals the sphere
 dimension for all n≥1, including the true circle. -/
theorem actual_weighted_gap_zero (p : E) (hp : ‖p‖=1) :
    weightedGap (n := n) p 0=(n : ℝ) := by
  have hupper := actual_weighted_gap_le_transverse_of_unit_axis (n := n) p hp 0
  rw [roundTiltMinimum_zero_field] at hupper
  exact le_antisymm hupper (actual_weighted_gap_zero_ge_dimension p hp)
end DFLPhysicalGap
