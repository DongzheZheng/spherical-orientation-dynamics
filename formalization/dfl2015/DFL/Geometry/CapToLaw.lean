import DFL.Geometry.ThreeVolume

/-!
# From the cap-volume calculation to the positive part of the coordinate law

The geometric cap-volume formula follows from the genuine Fubini evaluation.
These results cover actual coordinate-law intervals, not a custom density
definition.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

theorem sphereCapThree_area_real_of_volume_formula (t : ℝ)
    (hvol : (volume (coneCapThree t)).toReal =
      (2 * Real.pi / 3) * (1 - t)) :
    (area 3).real (sphereCapThree t) = 2 * Real.pi * (1 - t) := by
  rw [Measure.real, area_sphereCapThree]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hvol]
  ring

theorem coordinateLaw_three_Ioi (t : ℝ) :
    coordinateLaw 3 three_pos (Set.Ioi t) = area 3 (sphereCapThree t) := by
  rw [coordinateLaw, Measure.map_apply (continuous_coordinate 3 three_pos).measurable
    measurableSet_Ioi]
  rfl

/-- A compiled cap formula on the original three-dimensional Euclidean
sphere fixes the actual first-coordinate law on every positive half-axis
interval. No density assumption is made. -/
theorem coordinateLaw_three_positive_Ioc
    (hcap : ∀ t : ℝ, 0 < t → t < 1 →
      (volume (coneCapThree t)).toReal =
        (2 * Real.pi / 3) * (1 - t))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (coordinateLaw 3 three_pos).real (Set.Ioc a b) =
      2 * Real.pi * (b - a) := by
  letI : IsFiniteMeasure (area 3) := by
    change IsFiniteMeasure (volume : Measure (Ambient 3)).toSphere
    infer_instance
  letI : IsFiniteMeasure (coordinateLaw 3 three_pos) := by
    change IsFiniteMeasure ((area 3).map (coordinate 3 three_pos))
    infer_instance
  have hsubset : Set.Ioi b ⊆ Set.Ioi a := Set.Ioi_subset_Ioi hab.le
  have hdiff := MeasureTheory.measureReal_diff (μ := coordinateLaw 3 three_pos)
    hsubset measurableSet_Ioi
  rw [Set.Ioi_diff_Ioi] at hdiff
  rw [hdiff]
  change ((coordinateLaw 3 three_pos) (Set.Ioi a)).toReal -
      ((coordinateLaw 3 three_pos) (Set.Ioi b)).toReal =
        2 * Real.pi * (b - a)
  rw [coordinateLaw_three_Ioi a, coordinateLaw_three_Ioi b]
  have haArea : ((area 3) (sphereCapThree a)).toReal =
      2 * Real.pi * (1 - a) :=
    sphereCapThree_area_real_of_volume_formula a (hcap a ha (lt_trans hab hb))
  have hbArea : ((area 3) (sphereCapThree b)).toReal =
      2 * Real.pi * (1 - b) :=
    sphereCapThree_area_real_of_volume_formula b (hcap b (lt_trans ha hab) hb)
  rw [haArea, hbArea]
  ring

/-- Archimedes' cap-volume identity determines every positive interval of
the first-coordinate pushforward of the original sphere-area measure. -/
theorem coordinateLaw_three_positive_Ioc_actual
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (coordinateLaw 3 three_pos).real (Set.Ioc a b) =
      2 * Real.pi * (b - a) :=
  coordinateLaw_three_positive_Ioc
    (fun t ht ht1 => coneCapThree_volume_real t ht ht1) a b ha hab hb

theorem sphereCapThree_area_real (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (area 3).real (sphereCapThree t) = 2 * Real.pi * (1 - t) :=
  sphereCapThree_area_real_of_volume_formula t
    (coneCapThree_volume_real t ht ht1)

end

end DFL.Geometry
