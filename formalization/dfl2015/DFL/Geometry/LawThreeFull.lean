import DFL.Geometry.LawThreeBoundary
import DFL.Geometry.LawThreeTarget

/-!
# Full first-coordinate pushforward of the original two-sphere

The equality below compares two independently constructed Borel measures:
the pushforward of `volume.toSphere` and a constant-density restriction of
Lebesgue measure. It follows from equality on all closed lower rays.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

private instance : IsFiniteMeasure (coordinateLaw 3 three_pos) := by
  change IsFiniteMeasure ((area 3).map (coordinate 3 three_pos))
  infer_instance

private instance : IsFiniteMeasure targetCoordinateLawThree := by
  have hvol : (volume : Measure ℝ) (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    simp
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr hvol
  unfold targetCoordinateLawThree
  exact (volume.restrict (Set.Icc (-1 : ℝ) 1)).smul_finite
    ENNReal.ofReal_ne_top

/-- The physical two-sphere has uniform first-coordinate area law `2π dt`
on `[-1,1]`. Here the left side is the actual `volume.toSphere` pushforward. -/
theorem coordinateLaw_three_eq_target :
    coordinateLaw 3 three_pos = targetCoordinateLawThree := by
  apply Measure.ext_of_Iic
  intro t
  apply (measureReal_eq_measureReal_iff).mp
  by_cases hlow : t < -1
  · rw [coordinateLaw_three_Iic_low_real t hlow,
      targetCoordinateLawThree_Iic_low t hlow]
  have hleft : -1 ≤ t := le_of_not_gt hlow
  by_cases hnegone : t = -1
  · subst t
    rw [coordinateLaw_three_Iic_neg_one_real,
      targetCoordinateLawThree_Iic_middle (-1) le_rfl (by norm_num)]
    ring
  have hleft' : -1 < t := lt_of_le_of_ne hleft (Ne.symm hnegone)
  by_cases hneg : t < 0
  · rw [coordinateLaw_three_Iic_neg_real t hleft' hneg,
      targetCoordinateLawThree_Iic_middle t hleft (by linarith)]
  have hnonneg : 0 ≤ t := le_of_not_gt hneg
  by_cases hzero : t = 0
  · subst t
    rw [coordinateLaw_three_Iic_zero_real,
      targetCoordinateLawThree_Iic_middle 0 (by norm_num) (by norm_num)]
    ring
  have hpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  by_cases hhigh : 1 ≤ t
  · rw [coordinateLaw_three_Iic_high_real t hhigh,
      targetCoordinateLawThree_Iic_high t hhigh]
  have hlt : t < 1 := lt_of_not_ge hhigh
  rw [coordinateLaw_three_Iic_pos_real t hpos hlt,
    targetCoordinateLawThree_Iic_middle t hleft hlt.le]

/-- The exact geometric bridge in the form used by the physical-moment
interface. The multiplier is independent of the external field. -/
theorem coordinateLaw_three_eq_smul_volume :
    coordinateLaw 3 three_pos =
      ENNReal.ofReal (2 * Real.pi) •
        (volume.restrict (Set.Icc (-1 : ℝ) 1)) := by
  exact coordinateLaw_three_eq_target

end

end DFL.Geometry
