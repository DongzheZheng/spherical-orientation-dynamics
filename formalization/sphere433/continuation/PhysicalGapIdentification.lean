import continuation.FullSphereFirstLower
import continuation.CircleGapEquality
import continuation.PhysicalGapZeroExact
import continuation.PhysicalGapEven

/-! Identification of the original complete physical-sphere first positive
Rayleigh gap with the actual transverse auxiliary minimum, all dimensions
and all real fields. The scalar rate properties now refer to this genuine
whole-domain gap. First-eigenspace classification is a separate theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLPhysicalLatitude DFLSphere DFLTransverseSphere
namespace DFLPhysicalGap

def physicalGap (k : ℕ) (r : ℝ) : ℝ :=
  weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r

private theorem physicalGap_eq_transverse_nonnegative (k : ℕ) (r : ℝ) (hr : 0≤r) :
    physicalGap k r=roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
  by_cases hk : k=0
  · subst k
    simpa only [physicalGap,DFLCircleOdd.circleAxis,Nat.zero_add,Nat.cast_zero,zero_add]
      using actual_circle_gap_eq_transverse r
  by_cases hr0 : r=0
  · subst r
    unfold physicalGap
    rw [actual_weighted_gap_zero _ (by simp),roundTiltMinimum_zero_field]
    push_cast
    rfl
  apply le_antisymm
  · simpa only [physicalGap,Nat.cast_add,Nat.cast_one] using
      actual_weighted_gap_le_transverse_of_unit_axis (n := k+1)
        (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r
  · exact DFLFullSphereFirst.actual_weighted_gap_ge_transverse k (by omega) r (lt_of_le_of_ne hr (Ne.symm hr0))

/-- The original complete physical weighted gap equals the genuine
transverse minimum, on every S^(k+1), for every real field. -/
theorem actual_physical_gap_eq_transverse (k : ℕ) (r : ℝ) :
    physicalGap k r=roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
  by_cases hr : 0≤r
  · exact physicalGap_eq_transverse_nonnegative k r hr
  have hneg : 0≤-r := by linarith
  have hgap : physicalGap k (-r)=physicalGap k r :=
    actual_weighted_gap_even (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r
  rw [← hgap,physicalGap_eq_transverse_nonnegative k (-r) hneg,roundTiltMinimum_even_r]

/-- Exact zero-field value of the same complete physical gap. -/
theorem actual_physical_gap_zero (k : ℕ) : physicalGap k 0=(k+1 : ℝ) := by
  rw [actual_physical_gap_eq_transverse,roundTiltMinimum_zero_field]

/-- Field reversal preserves the complete physical gap. -/
theorem actual_physical_gap_even (k : ℕ) (r : ℝ) : physicalGap k (-r)=physicalGap k r := by
  rw [actual_physical_gap_eq_transverse,actual_physical_gap_eq_transverse,roundTiltMinimum_even_r]

/-- The original whole-sphere optimal rate strictly increases on [0,∞). -/
theorem actual_physical_gap_strictMonoOn (k : ℕ) :
    StrictMonoOn (physicalGap k) (Ici 0) := by
  have hf : physicalGap k=(fun r => roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)) :=
    funext (actual_physical_gap_eq_transverse k)
  rw [hf]
  simpa only [Nat.cast_add,Nat.cast_one] using roundTiltMinimum_physical_strictMonoOn (k+1) (k+1 : ℝ)

/-- C¹ regularity of the actual complete physical spectral gap. -/
theorem actual_physical_gap_contDiff_one (k : ℕ) : ContDiff ℝ 1 (physicalGap k) := by
  have hf : physicalGap k=(fun r => roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)) :=
    funext (actual_physical_gap_eq_transverse k)
  rw [hf]
  exact roundTiltMinimum_contDiff_one_r (k+1) (k+1 : ℝ) ((k+1 : ℝ)/2)

/-- The actual complete physical gap has strictly positive derivative
at every positive field, in every sphere dimension at least one. -/
theorem actual_physical_gap_deriv_pos (k : ℕ) (r : ℝ) (hr : 0<r) :
    0<deriv (physicalGap k) r := by
  have hf : physicalGap k=(fun s => roundTiltMinimum (k+1) (k+1 : ℝ) s ((k+1 : ℝ)/2)) :=
    funext (actual_physical_gap_eq_transverse k)
  rw [hf]
  have ht : (((k+1+2 : ℕ) : ℝ)/2-1)=(k+1 : ℝ)/2 := by push_cast; ring
  have h := roundTiltMinimum_deriv_r_pos_full (k+1) (k+1 : ℝ) 1 r
    (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]) hr
  simpa only [ht] using h

/-- The actual complete physical gap has zero field derivative at zero. -/
theorem actual_physical_gap_deriv_zero (k : ℕ) : deriv (physicalGap k) 0=0 := by
  have hf : physicalGap k=(fun r => roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)) :=
    funext (actual_physical_gap_eq_transverse k)
  rw [hf]
  exact roundTiltMinimum_deriv_r_zero (k+1) (k+1 : ℝ) ((k+1 : ℝ)/2)

/-- Royer's original zero-field lower bound holds for every real field;
it is strict at every nonzero field. -/
theorem actual_physical_gap_above_dimension (k : ℕ) (r : ℝ) (hr : r≠0) :
    (k+1 : ℝ)<physicalGap k r := by
  rw [actual_physical_gap_eq_transverse]
  simpa only [Nat.cast_add,Nat.cast_one] using
    roundTiltMinimum_physical_above_baseline (k+1) (k+1 : ℝ) r hr
end DFLPhysicalGap
