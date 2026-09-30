import continuation.TransverseFirstMinimumUpper
import continuation.PhysicalGapFullDomain
import continuation.TiltRateContinuity

/-! Complete physical circle gap identification, including all real fields.
The true reflection parity lower bound and actual transverse trial-state
upper bound refer to the same attained whole-domain minimum. -/
noncomputable section
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLTransverseSphere DFLSphere DFLCircleOdd
namespace DFLPhysicalGap

/-- The true full-domain weighted circle gap equals the original transverse
auxiliary minimum. This equality includes the zero-field endpoint. -/
theorem actual_circle_gap_eq_transverse (r : ℝ) :
    weightedGap (n := 1) circleAxis r=roundTiltMinimum 1 1 r (1/2) := by
  let a : CircleAmbient := EuclideanSpace.single 1 1
  have hp : ‖circleAxis‖=1 := by simp [circleAxis]
  have ha : ‖a‖=1 := by simp [a]
  have hpa : ⟪a,circleAxis⟫_ℝ=0 := by
    simp [a,circleAxis,EuclideanSpace.inner_single_left]
  have hupper := actual_weighted_gap_le_transverse (n := 1) circleAxis a hp ha hpa r
  exact le_antisymm (by simpa only [Nat.cast_one] using hupper)
    (actual_circle_gap_ge_transverse r)

/-- The actual physical circle gap strictly increases on nonnegative fields. -/
theorem actual_circle_gap_strictMonoOn :
    StrictMonoOn (fun r => weightedGap (n := 1) circleAxis r) (Ici 0) := by
  have hf : (fun r => weightedGap (n := 1) circleAxis r)=
      (fun r => roundTiltMinimum 1 1 r (1/2)) := funext actual_circle_gap_eq_transverse
  rw [hf]
  simpa only [Nat.cast_one] using roundTiltMinimum_physical_strictMonoOn 1 1

/-- The original complete circle rate is C¹ in its field parameter. -/
theorem actual_circle_gap_contDiff_one :
    ContDiff ℝ 1 (fun r => weightedGap (n := 1) circleAxis r) := by
  have hf : (fun r => weightedGap (n := 1) circleAxis r)=
      (fun r => roundTiltMinimum 1 1 r (1/2)) := funext actual_circle_gap_eq_transverse
  rw [hf]
  exact roundTiltMinimum_contDiff_one_r 1 1 (1/2)

/-- The complete circle gap has strictly positive field derivative for r>0. -/
theorem actual_circle_gap_deriv_pos (r : ℝ) (hr : 0<r) :
    0<deriv (fun s => weightedGap (n := 1) circleAxis s) r := by
  have hf : (fun s => weightedGap (n := 1) circleAxis s)=
      (fun s => roundTiltMinimum 1 1 s (1/2)) := funext actual_circle_gap_eq_transverse
  rw [hf]
  have h := roundTiltMinimum_deriv_r_pos_full 1 1 1 r (by norm_num) (by norm_num) hr
  norm_num at h
  exact h

/-- The same complete circle gap has its exact zero-field value. -/
theorem actual_circle_gap_zero : weightedGap (n := 1) circleAxis 0=1 := by
  rw [actual_circle_gap_eq_transverse,roundTiltMinimum_zero_field]

/-- Field reversal preserves the complete physical circle gap. -/
theorem actual_circle_gap_even (r : ℝ) :
    weightedGap (n := 1) circleAxis (-r)=weightedGap (n := 1) circleAxis r := by
  rw [actual_circle_gap_eq_transverse,actual_circle_gap_eq_transverse,roundTiltMinimum_even_r]

/-- The complete circle gap has zero derivative at zero field. -/
theorem actual_circle_gap_deriv_zero :
    deriv (fun r => weightedGap (n := 1) circleAxis r) 0=0 := by
  have hf : (fun r => weightedGap (n := 1) circleAxis r)=
      (fun r => roundTiltMinimum 1 1 r (1/2)) := funext actual_circle_gap_eq_transverse
  rw [hf]
  exact roundTiltMinimum_deriv_r_zero 1 1 (1/2)

end DFLPhysicalGap
