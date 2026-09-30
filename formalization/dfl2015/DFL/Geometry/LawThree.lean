import DFL.Geometry.CapSymmetryThree

/-!
# The actual first-coordinate law on the original two-sphere

We start from the cap and antipodal formulas for `volume.toSphere`, then
identify its full Borel pushforward. The target density is introduced only
on the right side of the final equality.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

private instance : IsFiniteMeasure (area 3) := by
  change IsFiniteMeasure (volume : Measure (Ambient 3)).toSphere
  infer_instance

private instance : IsFiniteMeasure (coordinateLaw 3 three_pos) := by
  change IsFiniteMeasure ((area 3).map (coordinate 3 three_pos))
  infer_instance

/-- The original cone-induced area of the unit two-sphere is `4π`. -/
theorem area_three_univ_real : (area 3).real Set.univ = 4 * Real.pi := by
  change ((volume : Measure (Ambient 3)).toSphere).real Set.univ =
    4 * Real.pi
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ (Ambient 3) = 3 := by simp
  rw [hdim]
  change (3 : ℝ) * (volume (Metric.ball (0 : Ambient 3) 1)).toReal =
    4 * Real.pi
  rw [EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

theorem coordinateLaw_three_univ_real :
    (coordinateLaw 3 three_pos).real Set.univ = 4 * Real.pi := by
  rw [coordinateLaw, Measure.real, Measure.map_apply
    (continuous_coordinate 3 three_pos).measurable MeasurableSet.univ]
  simpa only [Set.preimage_univ] using area_three_univ_real

/-- The lower tail follows from negation invariance of the actual
cone-induced sphere area measure. -/
theorem coordinateLaw_three_Iio_neg_real (t : ℝ)
    (ht : -1 < t) (ht0 : t < 0) :
    (coordinateLaw 3 three_pos).real (Set.Iio t) =
      2 * Real.pi * (1 + t) := by
  have hs : coordinateLaw 3 three_pos (Set.Iio t) =
      area 3 (lowerCapThree (-t)) := by
    rw [coordinateLaw, Measure.map_apply
      (continuous_coordinate 3 three_pos).measurable measurableSet_Iio]
    congr 1
    ext ω
    simp [lowerCapThree]
  have hpos : 0 < -t := by linarith
  have hlt : -t < 1 := by linarith
  change (coordinateLaw 3 three_pos (Set.Iio t)).toReal = _
  rw [hs, area_lowerCapThree_eq_upper]
  convert sphereCapThree_area_real (-t) hpos hlt using 1
  ring

/-- Right continuity of finite measures upgrades the strict lower-tail
formula to the closed lower tail. The proof uses an explicit interval
squeeze, including the possible atom at the threshold. -/
theorem coordinateLaw_three_Iic_neg_real (t : ℝ)
    (ht : -1 < t) (ht0 : t < 0) :
    (coordinateLaw 3 three_pos).real (Set.Iic t) =
      2 * Real.pi * (1 + t) := by
  let μ := coordinateLaw 3 three_pos
  let M := μ.real (Set.Iic t)
  let F := 2 * Real.pi * (1 + t)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hleft : F ≤ M := by
    have hsub : Set.Iio t ⊆ Set.Iic t := Set.Iio_subset_Iic le_rfl
    simpa only [μ, M, F, coordinateLaw_three_Iio_neg_real t ht ht0] using
      (measureReal_mono (μ := μ) hsub)
  apply le_antisymm ?_ hleft
  by_contra hnot
  have hgap : 0 < M - F := by
    have hlt : F < M := lt_of_not_ge hnot
    linarith
  let δ : ℝ := min (-t / 2) ((M - F) / (4 * Real.pi))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · linarith
    · positivity
  have hδbound : δ ≤ -t / 2 := min_le_left _ _
  have hδgap : δ ≤ (M - F) / (4 * Real.pi) := min_le_right _ _
  have htδ : -1 < t + δ := by linarith
  have htδ0 : t + δ < 0 := by linarith
  have hright : M ≤ μ.real (Set.Iio (t + δ)) := by
    exact measureReal_mono (μ := μ) (fun x hx => by
      exact lt_of_le_of_lt hx (lt_add_of_pos_right t hδ))
  rw [coordinateLaw_three_Iio_neg_real (t + δ) htδ htδ0] at hright
  have hsmall : 4 * Real.pi * δ ≤ M - F := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp at hδgap
    nlinarith [hδgap]
  dsimp [F] at hsmall ⊢
  nlinarith

theorem coordinateLaw_three_Iic_pos_real (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (coordinateLaw 3 three_pos).real (Set.Iic t) =
      2 * Real.pi * (1 + t) := by
  have htail : (coordinateLaw 3 three_pos).real (Set.Ioi t) =
      2 * Real.pi * (1 - t) := by
    change ((coordinateLaw 3 three_pos) (Set.Ioi t)).toReal = _
    rw [coordinateLaw_three_Ioi]
    exact sphereCapThree_area_real t ht ht1
  have hcompl := measureReal_compl (μ := coordinateLaw 3 three_pos)
    (s := Set.Ioi t) measurableSet_Ioi
  calc
    (coordinateLaw 3 three_pos).real (Set.Iic t) =
        4 * Real.pi - 2 * Real.pi * (1 - t) := by
          simpa only [Set.compl_Ioi, coordinateLaw_three_univ_real, htail] using hcompl
    _ = 2 * Real.pi * (1 + t) := by ring

theorem coordinateLaw_three_Iic_low_real (t : ℝ) (ht : t < -1) :
    (coordinateLaw 3 three_pos).real (Set.Iic t) = 0 := by
  have hsub : Set.Iic t ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and]
    intro hxlow
    have hxt : x ≤ t := hx
    linarith
  exact measureReal_mono_null hsub
    ((measureReal_eq_zero_iff).2
      (coordinateLaw_outside_Icc 3 three_pos))

theorem coordinateLaw_three_Iic_high_real (t : ℝ) (ht : 1 ≤ t) :
    (coordinateLaw 3 three_pos).real (Set.Iic t) =
      4 * Real.pi := by
  have hcap : sphereCapThree t = ∅ := by
    ext ω
    simp only [sphereCapThree, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    intro h
    have hcoord := (coordinate_mem_Icc 3 three_pos ω).2
    linarith
  have htail : (coordinateLaw 3 three_pos).real (Set.Ioi t) = 0 := by
    change ((coordinateLaw 3 three_pos) (Set.Ioi t)).toReal = 0
    rw [coordinateLaw_three_Ioi, hcap]
    simp
  have hcompl := measureReal_compl (μ := coordinateLaw 3 three_pos)
    (s := Set.Ioi t) measurableSet_Ioi
  simpa only [Set.compl_Ioi, coordinateLaw_three_univ_real, htail, sub_zero] using hcompl

end

end DFL.Geometry
