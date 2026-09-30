import DFL.Geometry.ThreeSections

/-!
# Cone volume of a cap on the original three-dimensional sphere

This file turns the genuine Fubini section identity into the Archimedes
cone-volume formula.  No spherical-coordinate pushforward is assumed.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Interval

noncomputable section

private def smallArea (t s : ℝ) : ℝ :=
  Real.pi * (s ^ 2 * ((1 - t ^ 2) / t ^ 2))

private def largeArea (s : ℝ) : ℝ :=
  Real.pi * (1 - s ^ 2)

private def sliceArea (t s : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) t).indicator (smallArea t) s +
    (Set.Ioc t 1).indicator largeArea s

private theorem small_section_volume
    (t s : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hs : 0 < s) (hst : s < t) :
    volume {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
      ENNReal.ofReal (smallArea t s) := by
  rw [coneCapThree_section_small t s ht ht1 hs hst,
    EuclideanSpace.volume_ball_fin_two]
  have hw : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hR : 0 ≤ s * Real.sqrt (1 - t ^ 2) / t := by positivity
  unfold smallArea
  rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul' Real.pi_pos.le]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt hw]
  ring

private theorem large_section_volume
    (t s : ℝ) (ht : 0 < t) (hts : t ≤ s) (hs1 : s < 1) :
    volume {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
      ENNReal.ofReal (largeArea s) := by
  rw [coneCapThree_section_large t s ht hts hs1,
    EuclideanSpace.volume_ball_fin_two]
  have hw : 0 ≤ 1 - s ^ 2 := by nlinarith
  unfold largeArea
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul' Real.pi_pos.le, Real.sq_sqrt hw]
  congr 1
  ring

private theorem smallArea_at_threshold (t : ℝ) (ht : 0 < t) :
    smallArea t t = largeArea t := by
  unfold smallArea largeArea
  have htne : t ≠ 0 := ne_of_gt ht
  field_simp

private theorem sliceArea_nonneg (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (s : ℝ) :
    0 ≤ sliceArea t s := by
  unfold sliceArea
  apply add_nonneg
  · by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
    · rw [Set.indicator_of_mem hs]
      unfold smallArea
      have hw : 0 ≤ 1 - t ^ 2 := by nlinarith
      positivity
    · simp [hs]
  · by_cases hs : s ∈ Set.Ioc t 1
    · rw [Set.indicator_of_mem hs]
      unfold largeArea
      have hsq : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      exact mul_nonneg Real.pi_pos.le (by linarith)
    · simp [hs]

private theorem section_volume_eq_ofReal_sliceArea
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (s : ℝ) :
    volume {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
      ENNReal.ofReal (sliceArea t s) := by
  by_cases hsmall : s ∈ Set.Ioc (0 : ℝ) t
  · have hlarge : s ∉ Set.Ioc t 1 := by
      intro h
      exact (not_lt_of_ge hsmall.2) h.1
    by_cases hst : s < t
    · rw [small_section_volume t s ht ht1 hsmall.1 hst]
      simp [sliceArea, hsmall, hlarge]
    · have hseq : s = t := le_antisymm hsmall.2 (le_of_not_gt hst)
      subst s
      rw [large_section_volume t t ht le_rfl ht1]
      simp [sliceArea, Set.mem_Ioc, ht, smallArea_at_threshold t ht]
  · by_cases hlarge : s ∈ Set.Ioc t 1
    · have hsmall' : s ∉ Set.Ioc (0 : ℝ) t := hsmall
      by_cases hs1 : s < 1
      · rw [large_section_volume t s ht hlarge.1.le hs1]
        simp [sliceArea, hsmall', hlarge]
      · have hseq : s = 1 := le_antisymm hlarge.2 (le_of_not_gt hs1)
        subst s
        rw [coneCapThree_section_empty_of_one_le t 1 le_rfl]
        simp [sliceArea, hsmall', hlarge, largeArea]
    · by_cases hs0 : s ≤ 0
      · rw [coneCapThree_section_empty_of_nonpos t s ht hs0]
        simp [sliceArea, hsmall, hlarge]
      · have hs1 : 1 ≤ s := by
          by_contra h
          have hslt : s < 1 := lt_of_not_ge h
          have hspos : 0 < s := lt_of_not_ge hs0
          have hts : t < s := by
            by_contra h'
            exact hsmall ⟨hspos, le_of_not_gt h'⟩
          exact hlarge ⟨hts, hslt.le⟩
        rw [coneCapThree_section_empty_of_one_le t s hs1]
        simp [sliceArea, hsmall, hlarge]

private theorem sliceArea_integrable (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Integrable (sliceArea t) volume := by
  have hcsmall : Continuous (smallArea t) := by
    unfold smallArea
    fun_prop
  have hclarge : Continuous largeArea := by
    unfold largeArea
    fun_prop
  have hismall : IntervalIntegrable (smallArea t) volume (0 : ℝ) t :=
    hcsmall.intervalIntegrable _ _
  have hilarge : IntervalIntegrable largeArea volume t 1 :=
    hclarge.intervalIntegrable _ _
  have hsmallOn : IntegrableOn (smallArea t) (Set.Ioc (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 hismall
  have hlargeOn : IntegrableOn largeArea (Set.Ioc t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht1.le).1 hilarge
  exact (hsmallOn.integrable_indicator measurableSet_Ioc).add
    (hlargeOn.integrable_indicator measurableSet_Ioc)

private theorem sliceArea_integral (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∫ s : ℝ, sliceArea t s) = (2 * Real.pi / 3) * (1 - t) := by
  have hcsmall : Continuous (smallArea t) := by
    unfold smallArea
    fun_prop
  have hclarge : Continuous largeArea := by
    unfold largeArea
    fun_prop
  have hsmallOn : IntegrableOn (smallArea t) (Set.Ioc (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1
      (hcsmall.intervalIntegrable _ _)
  have hlargeOn : IntegrableOn largeArea (Set.Ioc t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht1.le).1
      (hclarge.intervalIntegrable _ _)
  unfold sliceArea
  rw [integral_add (hsmallOn.integrable_indicator measurableSet_Ioc)
      (hlargeOn.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le ht1.le]
  simpa only [smallArea, largeArea] using
    threeDimensionalConeCap_slice_integral t ht

/-- For `0<t<1`, the actual cone cut out by a spherical cap has the
Euclidean volume predicted by Archimedes' spherical-band formula. -/
theorem coneCapThree_volume_real (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (volume (coneCapThree t)).toReal =
      (2 * Real.pi / 3) * (1 - t) := by
  rw [coneCapThree_volume_fubini]
  have hpoint : ∀ s : ℝ,
      volume {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
        ENNReal.ofReal (sliceArea t s) :=
    section_volume_eq_ofReal_sliceArea t ht ht1
  simp_rw [hpoint]
  have hint : Integrable (sliceArea t) volume := sliceArea_integrable t ht ht1
  have hnonneg : 0 ≤ᵐ[volume] sliceArea t :=
    Filter.Eventually.of_forall (sliceArea_nonneg t ht ht1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  have hIntNonneg : 0 ≤ ∫ s : ℝ, sliceArea t s :=
    integral_nonneg_of_ae hnonneg
  rw [ENNReal.toReal_ofReal hIntNonneg]
  exact sliceArea_integral t ht ht1

end

end DFL.Geometry
