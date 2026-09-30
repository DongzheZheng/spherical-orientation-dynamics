import DFL.Geometry.SuccCapSliceFormula

/-!
# Real-variable form of the genuine cap Fubini kernel

The original sphere cap has an exact nonnegative real slice function in
every dimension. This removes the extended-real integral and isolates
the remaining one-dimensional beta identity.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

def gammaBallConst (m : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1)

theorem gammaBallConst_pos (m : ℕ) : 0 < gammaBallConst m := by
  unfold gammaBallConst
  have harg : 0 < (m : ℝ) / 2 + 1 := by positivity
  exact div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) m)
    (Real.Gamma_pos_of_pos harg)

private theorem gammaBallConst_nonneg (m : ℕ) : 0 ≤ gammaBallConst m := by
  unfold gammaBallConst
  have harg : 0 < (m : ℝ) / 2 + 1 := by positivity
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) m)
    (Real.Gamma_pos_of_pos harg).le

def smallGammaSlice (m : ℕ) (t s : ℝ) : ℝ :=
  (s * Real.sqrt (1 - t ^ 2) / t) ^ m * gammaBallConst m

def largeGammaSlice (m : ℕ) (s : ℝ) : ℝ :=
  (Real.sqrt (1 - s ^ 2)) ^ m * gammaBallConst m

def realCapKernel (m : ℕ) (t s : ℝ) : ℝ :=
  if 0 < s ∧ s < t then smallGammaSlice m t s
  else if t ≤ s ∧ s < 1 then largeGammaSlice m s
  else 0

theorem scalarCapKernel_eq_ofReal_realCapKernel
    (m : ℕ) (t s : ℝ) (ht : 0 < t) :
    scalarCapKernel m t s = ENNReal.ofReal (realCapKernel m t s) := by
  unfold scalarCapKernel realCapKernel
  split_ifs with hs hl
  · have hr : 0 ≤ s * Real.sqrt (1 - t ^ 2) / t := by
      have hs0 : 0 < s := hs.1
      positivity
    unfold transverseBallVolume smallGammaSlice
    rw [← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (pow_nonneg hr m)]
    rfl
  · have hr : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
    unfold transverseBallVolume largeGammaSlice
    rw [← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (pow_nonneg hr m)]
    rfl
  · simp

private theorem realCapKernel_indicators (m : ℕ) (t : ℝ) :
    realCapKernel m t =
      (Set.Ioo (0 : ℝ) t).indicator (smallGammaSlice m t) +
        (Set.Ico t 1).indicator (largeGammaSlice m) := by
  funext s
  by_cases hs : 0 < s ∧ s < t
  · have hl : ¬(t ≤ s ∧ s < 1) := by
      rintro ⟨hts, -⟩
      exact (not_lt_of_ge hts) hs.2
    simp [realCapKernel, hs, hl, Set.indicator]
  · by_cases hl : t ≤ s ∧ s < 1
    · simp [realCapKernel, hs, hl, Set.indicator]
    · simp [realCapKernel, hs, hl, Set.indicator]

private theorem realCapKernel_integrable (m : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    Integrable (realCapKernel m t) volume := by
  have hcsmall : Continuous (smallGammaSlice m t) := by
    unfold smallGammaSlice
    fun_prop
  have hclarge : Continuous (largeGammaSlice m) := by
    unfold largeGammaSlice
    fun_prop
  have hsmallOn : IntegrableOn (smallGammaSlice m t)
      (Set.Ioo (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1
      (hcsmall.intervalIntegrable _ _)
  have hlargeOn : IntegrableOn (largeGammaSlice m)
      (Set.Ico t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht1.le).1
      (hclarge.intervalIntegrable _ _)
  rw [realCapKernel_indicators]
  exact (hsmallOn.integrable_indicator measurableSet_Ioo).add
    (hlargeOn.integrable_indicator measurableSet_Ico)

private theorem realCapKernel_nonneg (m : ℕ) (t s : ℝ)
    (ht : 0 < t) : 0 ≤ realCapKernel m t s := by
  unfold realCapKernel
  split_ifs with hs hl
  · unfold smallGammaSlice
    have hr : 0 ≤ s * Real.sqrt (1 - t ^ 2) / t := by
      have hs0 : 0 < s := hs.1
      positivity
    exact mul_nonneg (pow_nonneg hr m) (gammaBallConst_nonneg m)
  · unfold largeGammaSlice
    exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) m)
      (gammaBallConst_nonneg m)
  · rfl

/-- The exact original sphere cap kernel, converted from an extended-real
Lebesgue integral into two ordinary real interval integrals. -/
theorem scalarCapKernel_lintegral_real (m : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ s : ℝ, scalarCapKernel m t s).toReal =
      (∫ s in (0 : ℝ)..t, smallGammaSlice m t s) +
        (∫ s in t..1, largeGammaSlice m s) := by
  have hint := realCapKernel_integrable m t ht ht1
  have hnonneg : 0 ≤ᵐ[volume] realCapKernel m t :=
    Filter.Eventually.of_forall (realCapKernel_nonneg m t · ht)
  simp_rw [scalarCapKernel_eq_ofReal_realCapKernel m t _ ht]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  have hIntNonneg : 0 ≤ ∫ s : ℝ, realCapKernel m t s :=
    integral_nonneg_of_ae hnonneg
  rw [ENNReal.toReal_ofReal hIntNonneg]
  have hcsmall : Continuous (smallGammaSlice m t) := by
    unfold smallGammaSlice
    fun_prop
  have hclarge : Continuous (largeGammaSlice m) := by
    unfold largeGammaSlice
    fun_prop
  have hsmallOn : IntegrableOn (smallGammaSlice m t)
      (Set.Ioo (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1
      (hcsmall.intervalIntegrable _ _)
  have hlargeOn : IntegrableOn (largeGammaSlice m)
      (Set.Ico t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht1.le).1
      (hclarge.intervalIntegrable _ _)
  rw [realCapKernel_indicators]
  simp only [Pi.add_apply]
  rw [integral_add (hsmallOn.integrable_indicator measurableSet_Ioo)
      (hlargeOn.integrable_indicator measurableSet_Ico),
    integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ico,
    ← integral_Ioc_eq_integral_Ioo,
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le ht1.le]

/-- The lower-cone part of the general-dimensional cap Fubini formula
has an elementary polynomial antiderivative. -/
theorem smallGammaSlice_integral (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, smallGammaSlice m t s) =
      t * (Real.sqrt (1 - t ^ 2)) ^ m * gammaBallConst m / (m + 1) := by
  have hfun : (fun s : ℝ => smallGammaSlice m t s) =
      fun s => s ^ m * ((Real.sqrt (1 - t ^ 2) / t) ^ m * gammaBallConst m) := by
    funext s
    simp only [smallGammaSlice]
    rw [mul_div_assoc, mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_mul_const, integral_pow]
  have htne : t ≠ 0 := ne_of_gt ht
  have hden : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [zero_pow (by omega : m + 1 ≠ 0), sub_zero]
  rw [div_pow]
  field_simp
  ring

end

end DFL.Geometry
