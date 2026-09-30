import DFL.Geometry.CircleSqrtIntegral

/-!
# Evaluation of the genuine cap on the unit circle

The Fubini kernel from the original cone-induced circle is integrated in
ordinary real variables. This gives an actual geometric cap law, not a
postulated arcsine density.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

private def smallCircleSlice (t s : ℝ) : ℝ :=
  2 * (s * Real.sqrt (1 - t ^ 2) / t)

private def largeCircleSlice (s : ℝ) : ℝ :=
  2 * Real.sqrt (1 - s ^ 2)

private theorem circleSliceReal_indicators (t : ℝ) :
    circleSliceReal t =
      (Set.Ioo (0 : ℝ) t).indicator (smallCircleSlice t) +
        (Set.Ico t 1).indicator largeCircleSlice := by
  funext s
  by_cases hs : 0 < s ∧ s < t
  · have hl : ¬(t ≤ s ∧ s < 1) := by
      rintro ⟨hts, -⟩
      exact (not_lt_of_ge hts) hs.2
    simp [circleSliceReal, smallCircleSlice, hs, hl, Set.indicator]
  · by_cases hl : t ≤ s ∧ s < 1
    · simp [circleSliceReal, largeCircleSlice, hs, hl, Set.indicator]
    · simp [circleSliceReal, hs, hl, Set.indicator]

private theorem circleSliceReal_integrable (t : ℝ) (ht : 0 < t)
    (ht1 : t < 1) : Integrable (circleSliceReal t) volume := by
  have hcsmall : Continuous (smallCircleSlice t) := by
    unfold smallCircleSlice
    fun_prop
  have hclarge : Continuous largeCircleSlice := by
    unfold largeCircleSlice
    fun_prop
  have hsmallOn : IntegrableOn (smallCircleSlice t) (Set.Ioo (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1
      (hcsmall.intervalIntegrable _ _)
  have hlargeOn : IntegrableOn largeCircleSlice (Set.Ico t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht1.le).1
      (hclarge.intervalIntegrable _ _)
  rw [circleSliceReal_indicators]
  exact (hsmallOn.integrable_indicator measurableSet_Ioo).add
    (hlargeOn.integrable_indicator measurableSet_Ico)

private theorem circleSliceReal_nonneg (t : ℝ) (ht : 0 < t)
    (s : ℝ) : 0 ≤ circleSliceReal t s := by
  unfold circleSliceReal
  split_ifs with hs hl
  · have hs0 : 0 < s := hs.1
    positivity
  · positivity
  · rfl

private theorem smallCircleSlice_integral (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, smallCircleSlice t s) =
      t * Real.sqrt (1 - t ^ 2) := by
  have htne : t ≠ 0 := ne_of_gt ht
  unfold smallCircleSlice
  have hfun : (fun s : ℝ => 2 * (s * Real.sqrt (1 - t ^ 2) / t)) =
      (fun s : ℝ => (2 * Real.sqrt (1 - t ^ 2) / t) * s) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_id]
  field_simp
  ring

private theorem largeCircleSlice_integral (t : ℝ)
    (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in t..1, largeCircleSlice s) =
      Real.arccos t - t * Real.sqrt (1 - t ^ 2) := by
  unfold largeCircleSlice
  rw [intervalIntegral.integral_const_mul,
    integral_sqrt_one_sub_sq_to_one t ht ht1]
  ring

theorem circleSliceReal_integral (t : ℝ) (ht : 0 < t)
    (ht1 : t < 1) :
    (∫ s : ℝ, circleSliceReal t s) = Real.arccos t := by
  have hcsmall : Continuous (smallCircleSlice t) := by
    unfold smallCircleSlice
    fun_prop
  have hclarge : Continuous largeCircleSlice := by
    unfold largeCircleSlice
    fun_prop
  have hsmallOn : IntegrableOn (smallCircleSlice t) (Set.Ioo (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1
      (hcsmall.intervalIntegrable _ _)
  have hlargeOn : IntegrableOn largeCircleSlice (Set.Ico t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht1.le).1
      (hclarge.intervalIntegrable _ _)
  rw [circleSliceReal_indicators]
  simp only [Pi.add_apply]
  rw [integral_add (hsmallOn.integrable_indicator measurableSet_Ioo)
      (hlargeOn.integrable_indicator measurableSet_Ico),
    integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ico,
    ← integral_Ioc_eq_integral_Ioo,
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le ht1.le,
    smallCircleSlice_integral t ht,
    largeCircleSlice_integral t (by linarith) ht1.le]
  ring

theorem coordinateLaw_two_Ioi_real (t : ℝ) (ht : 0 < t)
    (ht1 : t < 1) :
    (coordinateLaw 2 (by decide)).real (Set.Ioi t) =
      2 * Real.arccos t := by
  have hint := circleSliceReal_integrable t ht ht1
  have hnonneg : 0 ≤ᵐ[volume] circleSliceReal t :=
    Filter.Eventually.of_forall (circleSliceReal_nonneg t ht)
  change ((coordinateLaw 2 (by decide)) (Set.Ioi t)).toReal = _
  rw [coordinateLaw_two_Ioi_circle_kernel t ht ht1,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  have hIntNonneg : 0 ≤ ∫ s : ℝ, circleSliceReal t s :=
    integral_nonneg_of_ae hnonneg
  rw [ENNReal.toReal_ofReal hIntNonneg,
    circleSliceReal_integral t ht ht1]

end

end DFL.Geometry
