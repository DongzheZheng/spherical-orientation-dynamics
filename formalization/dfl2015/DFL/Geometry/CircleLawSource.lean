import DFL.Geometry.CircleCapVolume
import DFL.Geometry.SuccCapSymmetry

/-!
# Total mass and antipodal tails of the actual unit-circle coordinate law

These identities come from mathlib's `volume.toSphere` and the genuine cap
calculation. They do not refer to the comparison Chebyshev measure.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

private instance : IsFiniteMeasure (area 2) := by
  change IsFiniteMeasure (volume : Measure (Ambient 2)).toSphere
  infer_instance

private instance : IsFiniteMeasure (coordinateLaw 2 two_pos) := by
  change IsFiniteMeasure ((area 2).map (coordinate 2 two_pos))
  infer_instance

theorem area_two_univ_real : (area 2).real Set.univ = 2 * Real.pi := by
  change ((volume : Measure (Ambient 2)).toSphere).real Set.univ =
    2 * Real.pi
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ (Ambient 2) = 2 := by simp
  rw [hdim]
  change (2 : ℝ) * (volume (Metric.ball (0 : Ambient 2) 1)).toReal =
    2 * Real.pi
  rw [EuclideanSpace.volume_ball_fin_two]
  simp only [ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal Real.pi_pos.le]

theorem coordinateLaw_two_univ_real :
    (coordinateLaw 2 two_pos).real Set.univ = 2 * Real.pi := by
  rw [coordinateLaw, Measure.real, Measure.map_apply
    (continuous_coordinate 2 two_pos).measurable MeasurableSet.univ]
  simpa only [Set.preimage_univ] using area_two_univ_real

theorem coordinateLaw_two_Iio_neg_real (t : ℝ)
    (ht : -1 < t) (ht0 : t < 0) :
    (coordinateLaw 2 two_pos).real (Set.Iio t) =
      2 * Real.arccos (-t) := by
  have hs : coordinateLaw 2 two_pos (Set.Iio t) =
      area 2 (lowerCapSucc 1 (-t)) := by
    rw [coordinateLaw, Measure.map_apply
      (continuous_coordinate 2 two_pos).measurable measurableSet_Iio]
    congr 1
    ext ω
    simp [lowerCapSucc]
  have hpos : 0 < -t := by linarith
  have hlt : -t < 1 := by linarith
  change (coordinateLaw 2 two_pos (Set.Iio t)).toReal = _
  rw [hs, area_lowerCapSucc_eq_upper]
  have hcap : (area 2).real (sphereCapSucc 1 (-t)) =
      2 * Real.arccos (-t) := by
    have hmap := coordinateLaw_two_Ioi_real (-t) hpos hlt
    change ((coordinateLaw 2 two_pos) (Set.Ioi (-t))).toReal = _ at hmap
    rw [coordinateLaw, Measure.map_apply
      (continuous_coordinate 2 two_pos).measurable measurableSet_Ioi] at hmap
    exact hmap
  exact hcap

end

end DFL.Geometry
