import DFL.Geometry.LawThree

/-!
# Boundary values of the genuine two-sphere coordinate distribution

The cap law gives linear tails away from the equator and poles. Finite
measure and monotonicity force the two boundary CDF values below, without
assuming atomlessness or a preassigned density.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

private instance : IsFiniteMeasure (coordinateLaw 3 three_pos) := by
  change IsFiniteMeasure ((area 3).map (coordinate 3 three_pos))
  infer_instance

/-- The actual sphere has lower coordinate mass `2π` through the equator,
including any a priori possible atom there. -/
theorem coordinateLaw_three_Iic_zero_real :
    (coordinateLaw 3 three_pos).real (Set.Iic (0 : ℝ)) =
      2 * Real.pi := by
  let μ := coordinateLaw 3 three_pos
  let M := μ.real (Set.Iic (0 : ℝ))
  have hπ : 0 < 2 * Real.pi := by positivity
  have hlow : 2 * Real.pi ≤ M := by
    by_contra hnot
    have hgap : 0 < 2 * Real.pi - M := by linarith
    let δ : ℝ := min (1 / 2) ((2 * Real.pi - M) / (4 * Real.pi))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1 / 2 := min_le_left _ _
    have hδgap : δ ≤ (2 * Real.pi - M) / (4 * Real.pi) := min_le_right _ _
    have ht : -1 < -δ := by linarith
    have ht0 : -δ < 0 := by linarith
    have hmono : μ.real (Set.Iic (-δ)) ≤ M :=
      measureReal_mono (μ := μ) (Set.Iic_subset_Iic.mpr (by linarith))
    rw [coordinateLaw_three_Iic_neg_real (-δ) ht ht0] at hmono
    have hsmall : 4 * Real.pi * δ ≤ 2 * Real.pi - M := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp at hδgap
      nlinarith
    dsimp [M] at hmono hsmall ⊢
    nlinarith
  have hupp : M ≤ 2 * Real.pi := by
    by_contra hnot
    have hgap : 0 < M - 2 * Real.pi := by linarith
    let δ : ℝ := min (1 / 2) ((M - 2 * Real.pi) / (4 * Real.pi))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1 / 2 := min_le_left _ _
    have hδgap : δ ≤ (M - 2 * Real.pi) / (4 * Real.pi) := min_le_right _ _
    have ht1 : δ < 1 := by linarith
    have htail : μ.real (Set.Ioi δ) = 2 * Real.pi * (1 - δ) := by
      change ((coordinateLaw 3 three_pos) (Set.Ioi δ)).toReal = _
      rw [coordinateLaw_three_Ioi]
      exact sphereCapThree_area_real δ hδ ht1
    have hcomp : μ.real (Set.Iic δ) =
        4 * Real.pi - 2 * Real.pi * (1 - δ) := by
      rw [← Set.compl_Ioi, measureReal_compl measurableSet_Ioi,
        coordinateLaw_three_univ_real, htail]
    have hmono : M ≤ μ.real (Set.Iic δ) :=
      measureReal_mono (μ := μ) (Set.Iic_subset_Iic.mpr hδ.le)
    rw [hcomp] at hmono
    have hsmall : 4 * Real.pi * δ ≤ M - 2 * Real.pi := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp at hδgap
      nlinarith
    dsimp [M] at hmono hsmall ⊢
    nlinarith
  exact le_antisymm hupp hlow

/-- The south pole has zero area in the true first-coordinate law. -/
theorem coordinateLaw_three_Iic_neg_one_real :
    (coordinateLaw 3 three_pos).real (Set.Iic (-1 : ℝ)) = 0 := by
  let μ := coordinateLaw 3 three_pos
  let M := μ.real (Set.Iic (-1 : ℝ))
  have hnonneg : 0 ≤ M := measureReal_nonneg
  have hupp : M ≤ 0 := by
    by_contra hnot
    have hgap : 0 < M := by linarith
    let δ : ℝ := min (1 / 2) (M / (4 * Real.pi))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1 / 2 := min_le_left _ _
    have hδgap : δ ≤ M / (4 * Real.pi) := min_le_right _ _
    have ht : -1 < -1 + δ := by linarith
    have ht0 : -1 + δ < 0 := by linarith
    have hmono : M ≤ μ.real (Set.Iic (-1 + δ)) :=
      measureReal_mono (μ := μ) (Set.Iic_subset_Iic.mpr (by linarith))
    rw [coordinateLaw_three_Iic_neg_real (-1 + δ) ht ht0] at hmono
    have hsmall : 4 * Real.pi * δ ≤ M := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp at hδgap
      nlinarith
    dsimp [M] at hmono hsmall ⊢
    nlinarith
  exact le_antisymm hupp hnonneg

end

end DFL.Geometry
