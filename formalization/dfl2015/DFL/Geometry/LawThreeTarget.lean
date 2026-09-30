import DFL.Geometry.LawThree

/-!
# The comparison measure for the three-dimensional latitude law

This is the constant-density measure on the physical interval. It is
introduced only to compare with the already constructed sphere pushforward.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

def targetCoordinateLawThree : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi) •
    (volume.restrict (Set.Icc (-1 : ℝ) 1))

private theorem targetCoordinateLawThree_real (s : Set ℝ)
    (hs : MeasurableSet s) :
    targetCoordinateLawThree.real s =
      2 * Real.pi * volume.real (s ∩ Set.Icc (-1 : ℝ) 1) := by
  unfold targetCoordinateLawThree
  rw [measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]

theorem targetCoordinateLawThree_Iic_low (t : ℝ) (ht : t < -1) :
    targetCoordinateLawThree.real (Set.Iic t) = 0 := by
  rw [targetCoordinateLawThree_real _ measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (-1 : ℝ) 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hxt, hx, -⟩
    linarith
  rw [hset]
  simp

theorem targetCoordinateLawThree_Iic_middle (t : ℝ)
    (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    targetCoordinateLawThree.real (Set.Iic t) =
      2 * Real.pi * (1 + t) := by
  rw [targetCoordinateLawThree_real _ measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (-1 : ℝ) 1 =
      Set.Icc (-1 : ℝ) t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hxt, hx, -⟩
      exact ⟨hx, hxt⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨hxt, hx, hxt.trans ht1⟩
  rw [hset]
  simp only [Measure.real]
  rw [Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ t - -1)]
  ring

theorem targetCoordinateLawThree_Iic_high (t : ℝ) (ht : 1 ≤ t) :
    targetCoordinateLawThree.real (Set.Iic t) =
      4 * Real.pi := by
  rw [targetCoordinateLawThree_real _ measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (-1 : ℝ) 1 =
      Set.Icc (-1 : ℝ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · exact And.right
    · intro hx
      exact ⟨hx.2.trans ht, hx⟩
  rw [hset]
  simp only [Measure.real]
  rw [Real.volume_Icc]
  norm_num
  ring

end

end DFL.Geometry
