import DFL.Geometry.MomentBridge

/-!
# From the genuine three-dimensional coordinate law to physical moments

This module isolates the final integration step.  Its hypothesis is the
equality of the actual cone-induced sphere coordinate law with Lebesgue
measure on `[-1,1]` scaled by `2π`.  The geometric proof of that law is in
separate modules; this theorem must not be read as an unconditional proof of
the sphere-level conjecture until that hypothesis is discharged.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Interval ENNReal

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

private theorem marginalWeight_three (r t : ℝ) :
    DFL.marginalWeight 3 r t = Real.exp (r * t) := by
  simp [DFL.marginalWeight]

/-- The exact integration consequence of the original sphere's uniform
first-coordinate law in dimension three.  The law is an explicit premise,
not an axiom introduced in the formalization. -/
theorem sphereMomentBridge_three_of_coordinateLaw
    (hLaw : coordinateLaw 3 three_pos =
      (ENNReal.ofReal (2 * Real.pi)) •
        (volume.restrict (Set.Icc (-1 : ℝ) 1))) :
    SphereMomentBridge 3 three_pos := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro r
  constructor
  · rw [spherePartition_eq_coordinateLaw_integral, hLaw, integral_smul_measure]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
    simp only [smul_eq_mul]
    congr 1
    change (∫ t in Set.Icc (-1 : ℝ) 1, Real.exp (r * t)) = DFL.partition 3 r
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    unfold DFL.partition
    apply intervalIntegral.integral_congr
    intro t _
    exact (marginalWeight_three r t).symm
  · rw [sphereFirstMoment_eq_coordinateLaw_integral, hLaw, integral_smul_measure]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
    simp only [smul_eq_mul]
    congr 1
    change (∫ t in Set.Icc (-1 : ℝ) 1, t * Real.exp (r * t)) =
      DFL.firstMoment 3 r
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    unfold DFL.firstMoment
    apply intervalIntegral.integral_congr
    intro t _
    simp only [marginalWeight_three]

/-- Once the genuine coordinate law is supplied, the original physical
two-sphere density curve has exactly one nondegenerate valley. -/
theorem sphere_isUnimodal_three_of_coordinateLaw
    (hLaw : coordinateLaw 3 three_pos =
      (ENNReal.ofReal (2 * Real.pi)) •
        (volume.restrict (Set.Icc (-1 : ℝ) 1))) :
    SphereIsUnimodal 3 three_pos :=
  sphere_isUnimodal_of_moment_bridge 3 (by decide)
    (sphereMomentBridge_three_of_coordinateLaw hLaw)

end

end DFL.Geometry
