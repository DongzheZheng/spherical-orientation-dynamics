import DFL.GCI.ComparisonTwoD

/-!
# Strict two-dimensional GCI comparison with the shifted mean

The energy Cauchy step in `AngularUpper2D` can be sharpened because the
explicit solution of the original represented weak equation cannot have a
derivative proportional to the sine test's derivative.  No regularity of an
arbitrary weak solution is added: coefficient uniqueness transfers the strict
result from the explicit weak solution to every represented weak solution.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private theorem explicitQ_not_proportional_cos
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      explicitQ r θ ≠ t * Real.cos θ := by
  by_contra hnone
  have hpoint (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      explicitQ r θ = t * Real.cos θ := by
    by_contra hne
    exact hnone ⟨θ, hθ, hne⟩
  have hmidmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hmid := hpoint (Real.pi / 2) hmidmem
  have hJne : explicitJ r ≠ 0 := (explicitJ_pos r).ne'
  have hJ : explicitJ r = Real.pi := by
    dsimp [explicitQ] at hmid
    simp only [Real.cos_pi_div_two, mul_zero,
      Real.exp_zero, mul_one] at hmid
    field_simp [hr.ne', hJne] at hmid
    linarith
  have hformula (θ : ℝ) :
      explicitQ r θ = (1 - Real.exp (-r * Real.cos θ)) / r := by
    unfold explicitQ
    rw [hJ]
    field_simp [hr.ne', Real.pi_ne_zero]
  have hzero := hpoint 0 ⟨le_rfl, Real.pi_pos.le⟩
  have hpi := hpoint Real.pi ⟨Real.pi_pos.le, le_rfl⟩
  have hzero' : (1 - Real.exp (-r)) / r = t := by
    simpa only [hformula, Real.cos_zero, mul_one] using hzero
  have hpi' : (1 - Real.exp r) / r = -t := by
    simpa only [hformula, Real.cos_pi, mul_neg, mul_one, neg_neg] using hpi
  have hzeroMul : 1 - Real.exp (-r) = t * r :=
    (div_eq_iff hr.ne').mp hzero'
  have hpiMul : 1 - Real.exp r = (-t) * r :=
    (div_eq_iff hr.ne').mp hpi'
  have hsum : Real.exp r + Real.exp (-r) = 2 := by
    linarith
  have hprod : Real.exp r * Real.exp (-r) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul :
      Real.exp r * Real.exp r + Real.exp r * Real.exp (-r) =
        2 * Real.exp r := by
    nlinarith [congrArg (fun x : ℝ => Real.exp r * x) hsum]
  have hsq : (Real.exp r - 1) ^ 2 = 0 := by
    nlinarith [hmul, hprod]
  have hEr : 1 < Real.exp r := by
    have := Real.exp_lt_exp.mpr hr
    simpa using this
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hEr.ne')]

/-- The exact energy Cauchy inequality is strict for the explicitly
constructed original represented weak solution at every positive field. -/
theorem explicit_solution_energy_cauchy_strict_twoD
    (r : ℝ) (hr : 0 < r) :
    (originalForcingNorm 2 r) ^ 2 <
      originalGCIDenominator 2 r (explicitState r) * twoDSineEnergy r := by
  let s := explicitState r
  let W := fun θ : ℝ => Real.exp (r * Real.cos θ)
  let q := explicitQ r
  let Z := originalForcingNorm 2 r
  let D := originalGCIDenominator 2 r s
  let T := twoDSineEnergy r
  have hs : OriginalWeakGCISolution 2 r s :=
    explicit_original_weak_solution_twoD r hr
  have hTpos : 0 < T := twoDSineEnergy_pos r
  let t : ℝ := Z / T
  have ht : t * T = Z := by
    dsimp [t]
    exact div_mul_cancel₀ _ hTpos.ne'
  have hWcont : Continuous W := by
    dsimp [W]
    fun_prop
  have hqcont : Continuous q := explicitQ_continuous r
  have hEint : IntervalIntegrable
      (fun θ : ℝ => W θ * (q θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    exact (hWcont.mul (hqcont.pow 2)).intervalIntegrable _ _
  have hCrossInt : IntervalIntegrable
      (fun θ : ℝ => W θ * q θ * Real.cos θ)
      volume (0 : ℝ) Real.pi := by
    exact ((hWcont.mul hqcont).mul Real.continuous_cos).intervalIntegrable _ _
  have hTint : IntervalIntegrable
      (fun θ : ℝ => W θ * (Real.cos θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    exact (hWcont.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have hEeq :
      (∫ θ in (0 : ℝ)..Real.pi, W θ * (q θ) ^ 2) = D := by
    calc
      _ = originalWeakForm 2 r s s := by
        simpa only [s, W, q, explicitState] using
          (twoD_energy_formula r s).symm
      _ = originalSourcePairing 2 r s := (hs.2 s hs.1).2.2
      _ = D := originalSourcePairing_eq_denominator 2 (by omega) r s
  have hCrossEq :
      (∫ θ in (0 : ℝ)..Real.pi,
        W θ * q θ * Real.cos θ) = Z := by
    calc
      _ = originalWeakForm 2 r s (sineTestState 2) := by
        rw [twoD_weakForm_sine]
        apply intervalIntegral.integral_congr
        intro θ _
        change W θ * q θ * Real.cos θ =
          (Real.exp (r * Real.cos θ) * Real.cos θ) * q θ
        dsimp [W]
        ring
      _ = originalSourcePairing 2 r (sineTestState 2) :=
        (hs.2 (sineTestState 2) (sineTestState_mem_energy 2 (by omega))).2.2
      _ = Z := sourcePairing_sine_eq_forcingNorm 2 r
  have hT_eq :
      (∫ θ in (0 : ℝ)..Real.pi,
        W θ * (Real.cos θ) ^ 2) = T := rfl
  have hQcont : ContinuousOn
      (fun θ : ℝ => W θ * (q θ - t * Real.cos θ) ^ 2)
      (Set.Icc (0 : ℝ) Real.pi) := by
    exact (hWcont.mul
      ((hqcont.sub (continuous_const.mul Real.continuous_cos)).pow 2)).continuousOn
  have hQpos : 0 < ∫ θ in (0 : ℝ)..Real.pi,
      W θ * (q θ - t * Real.cos θ) ^ 2 := by
    apply intervalIntegral.integral_pos Real.pi_pos hQcont
    · intro θ _
      exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
    · obtain ⟨θ, hθ, hne⟩ :=
        explicitQ_not_proportional_cos r hr t
      refine ⟨θ, hθ, ?_⟩
      exact mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  have hQeq :
      (∫ θ in (0 : ℝ)..Real.pi,
        W θ * (q θ - t * Real.cos θ) ^ 2) =
        D - (2 * t) * Z + t ^ 2 * T := by
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
          (W θ * (q θ) ^ 2 -
            (2 * t) * (W θ * q θ * Real.cos θ)) +
            t ^ 2 * (W θ * (Real.cos θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
            (hEint.sub (hCrossInt.const_mul (2 * t)))
            (hTint.const_mul (t ^ 2)),
          intervalIntegral.integral_sub hEint
            (hCrossInt.const_mul (2 * t)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          hEeq, hCrossEq, hT_eq]
  have hproduct :
      (∫ θ in (0 : ℝ)..Real.pi,
        W θ * (q θ - t * Real.cos θ) ^ 2) * T =
          D * T - Z ^ 2 := by
    rw [hQeq]
    calc
      (D - (2 * t) * Z + t ^ 2 * T) * T =
          D * T - (t * T) ^ 2 := by rw [← ht]; ring
      _ = D * T - Z ^ 2 := by rw [ht]
  have hpos := mul_pos hQpos hTpos
  dsimp [Z, D, T] at hproduct ⊢
  linarith

/-- The 2015 two-dimensional represented weak GCI coefficient lies
strictly below the exact dimension-four orientation mean. -/
theorem weak_solution_coefficient_lt_shift_mean_twoD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    originalGCICoefficient 2 r s < DFL.orientationMean 4 r := by
  let e := explicitState r
  have he : OriginalWeakGCISolution 2 r e :=
    explicit_original_weak_solution_twoD r hr
  have hD : 0 < originalGCIDenominator 2 r e :=
    weak_solution_denominator_pos 2 (by omega) r e he
  have hZ : 0 < originalForcingNorm 2 r :=
    originalForcingNorm_pos_of_weak_solution 2 (by omega) r e he
  have hT := twoDSineEnergy_eq_forcingNorm_add_shiftMoment r
  have hM := weak_solution_moment_identity_twoD r e he
  have hStrict := explicit_solution_energy_cauchy_strict_twoD r hr
  have hND : originalForcingNorm 2 r *
      originalGCINumerator 2 r e <
      originalGCIDenominator 2 r e * twoDShiftMoment r := by
    nlinarith [mul_nonneg hr.le hZ.le]
  have hCoeff : originalGCICoefficient 2 r e <
      twoDShiftMoment r / originalForcingNorm 2 r := by
    unfold originalGCICoefficient
    exact (div_lt_div_iff₀ hD hZ).2 (by nlinarith [hND])
  calc
    originalGCICoefficient 2 r s =
        originalGCICoefficient 2 r e :=
      weak_solution_coefficient_unique_twoD r hr s e hs he
    _ < twoDShiftMoment r / originalForcingNorm 2 r := hCoeff
    _ = DFL.orientationMean 4 r :=
      (orientationMean_four_eq_twoD_shift_ratio r).symm

/-- A constructed original represented weak solution realizes the full
strict two-dimensional chain, including coefficient uniqueness. -/
theorem original_GCI_twoD_strict_shift_chain
    (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution 2 r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution 2 r v →
        originalGCICoefficient 2 r v = originalGCICoefficient 2 r s) ∧
      0 < originalGCIDenominator 2 r s ∧
      0 < originalGCICoefficient 2 r s ∧
      originalGCICoefficient 2 r s < DFL.orientationMean 4 r ∧
      DFL.orientationMean 4 r < DFL.orientationMean 2 r := by
  obtain ⟨s, hs, huniq, hD, hpos⟩ :=
    original_GCI_twoD_exists_unique_positive r hr
  exact ⟨s, hs, huniq, hD, hpos,
    weak_solution_coefficient_lt_shift_mean_twoD r hr s hs,
    DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
      2 (by omega) hr⟩

end

end DFL.GCI
