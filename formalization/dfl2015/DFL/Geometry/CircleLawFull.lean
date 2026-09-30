import DFL.Geometry.CircleTargetLower

/-!
# The genuine circle-coordinate law

The first coordinate of Mathlib's original `volume.toSphere` measure on
the unit circle has the exact arcsine law on every Borel set. Both sides
are independently defined measures; equality follows from their
closed-lower-ray values.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

private instance : IsFiniteMeasure (coordinateLaw 2 two_pos) := by
  change IsFiniteMeasure ((area 2).map (coordinate 2 two_pos))
  infer_instance

private instance : IsFiniteMeasure
    ((2 : ENNReal) • Polynomial.Chebyshev.measureT) := by
  exact Measure.smul_finite Polynomial.Chebyshev.measureT (by norm_num)

/-- The pushforward of the original circle surface measure by its first
coordinate equals twice Mathlib's Chebyshev arcsine measure, as Borel
measures on all of `ℝ`. -/
theorem coordinateLaw_two_eq_two_smul_measureT :
    coordinateLaw 2 two_pos =
      (2 : ENNReal) • Polynomial.Chebyshev.measureT := by
  apply Measure.ext_of_Iic
    (coordinateLaw 2 two_pos)
    ((2 : ENNReal) • Polynomial.Chebyshev.measureT)
  intro t
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [measureReal_ennreal_smul_apply]
  norm_num only [ENNReal.toReal_ofNat]
  rcases lt_trichotomy t (-1 : ℝ) with hlow | heq | hgt
  · rw [coordinateLaw_two_Iic_low_real t hlow,
      measureT_Iic_low_real t hlow.le]
    ring
  · subst t
    rw [coordinateLaw_two_Iic_neg_one_real,
      measureT_Iic_low_real (-1) le_rfl]
    ring
  rcases lt_trichotomy t (0 : ℝ) with hneg | heq | hpos
  · rw [coordinateLaw_two_Iic_neg_real t hgt hneg,
      measureT_Iic_internal_real t ⟨hgt.le, by linarith⟩,
      Real.arccos_neg]
  · subst t
    rw [coordinateLaw_two_Iic_zero_real,
      measureT_Iic_internal_real 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1),
      Real.arccos_zero]
    ring
  rcases lt_trichotomy t (1 : ℝ) with hlt | heq | hhigh
  · rw [coordinateLaw_two_Iic_pos_real t hpos hlt,
      measureT_Iic_internal_real t ⟨by linarith, hlt.le⟩]
    ring
  · subst t
    rw [coordinateLaw_two_Iic_high_real 1 le_rfl,
      measureT_Iic_high_real 1 le_rfl]
  · rw [coordinateLaw_two_Iic_high_real t hhigh.le,
      measureT_Iic_high_real t hhigh.le]

end

end DFL.Geometry
