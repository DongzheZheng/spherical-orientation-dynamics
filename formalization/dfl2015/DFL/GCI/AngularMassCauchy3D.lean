import DFL.GCI.AngularMomentAll

/-!
# Original three-dimensional weighted mass and forcing Cauchy inequality

The weighted mass is expressed through the *same original* `H¹₀`
representative `u = sqrt(sin θ) g`.  This avoids assigning an arbitrary
auxiliary amplitude to the weak solution.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def threeDWeightedMass (r : ℝ) (s : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (r * Real.cos θ) * (momentPrimitive s θ) ^ 2

private def threeDForcingAmplitude (θ : ℝ) : ℝ :=
  Real.sin θ ^ (3 / 2 : ℝ)

private theorem threeDForcingAmplitude_continuous :
    Continuous threeDForcingAmplitude := by
  unfold threeDForcingAmplitude
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
    Real.continuous_sin

theorem threeDWeightedMass_integrable
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 3 s) :
    IntervalIntegrable
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        (momentPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  have hu := momentPrimitive_continuousOn 3 s hs
  have hw : ContinuousOn (fun θ : ℝ => Real.exp (r * Real.cos θ))
      (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ))).continuousOn
  exact (hw.mul (hu.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le

theorem threeD_denominator_mass_formula
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 3 s) :
    originalGCIDenominator 3 r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          threeDForcingAmplitude θ * momentPrimitive s θ := by
  rw [moment_denominator_formula 3 r s hs]
  apply intervalIntegral.integral_congr
  intro θ _
  norm_num [momentDenominatorWeight, threeDForcingAmplitude, halfPower]

theorem threeD_forcingNorm_mass_formula (r : ℝ) :
    originalForcingNorm 3 r =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (threeDForcingAmplitude θ) ^ 2 := by
  unfold originalForcingNorm
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hpow :
      (threeDForcingAmplitude θ) ^ 2 = (Real.sin θ) ^ 3 := by
    unfold threeDForcingAmplitude
    have h : (3 / 2 : ℝ) + 3 / 2 = 3 := by ring
    calc
      _ = (Real.sin θ) ^ (3 / 2 : ℝ) *
          (Real.sin θ) ^ (3 / 2 : ℝ) := by ring
      _ = (Real.sin θ) ^ ((3 / 2 : ℝ) + 3 / 2) :=
        (Real.rpow_add hsin _ _).symm
      _ = (Real.sin θ) ^ 3 := by
        rw [h]
        norm_num [Real.rpow_natCast]
  rw [angularWeight_eq_sin_pow 3 (by omega) r θ]
  norm_num at hpow ⊢
  rw [hpow]
  ring

/-- Original forcing pair versus the physical weak-solution mass in
ambient dimension three.  Both sides are finite from the original
represented weak domain. -/
theorem weak_solution_weighted_mass_cauchy_threeD
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s) :
    (originalGCIDenominator 3 r s) ^ 2 ≤
      originalForcingNorm 3 r * threeDWeightedMass r s := by
  have hZpos : 0 < originalForcingNorm 3 r :=
    originalForcingNorm_pos_of_weak_solution 3 (by omega) r s hs
  have hM := threeDWeightedMass_integrable r s hs.1
  have hu := momentPrimitive_continuousOn 3 s hs.1
  have hw : ContinuousOn (fun θ : ℝ => Real.exp (r * Real.cos θ))
      (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ))).continuousOn
  have hβ : ContinuousOn threeDForcingAmplitude
      (Set.Icc (0 : ℝ) Real.pi) :=
    threeDForcingAmplitude_continuous.continuousOn
  have hD : IntervalIntegrable
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        threeDForcingAmplitude θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (((hw.mul hβ).mul hu)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hZ : IntervalIntegrable
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        (threeDForcingAmplitude θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((hw.mul (hβ.pow 2))).intervalIntegrable_of_Icc Real.pi_pos.le
  let t : ℝ := originalGCIDenominator 3 r s / originalForcingNorm 3 r
  have ht : t * originalForcingNorm 3 r =
      originalGCIDenominator 3 r s := by
    dsimp [t]
    exact div_mul_cancel₀ _ hZpos.ne'
  have hqnonneg :
      0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (momentPrimitive s θ - t * threeDForcingAmplitude θ) ^ 2 := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hqexp :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (momentPrimitive s θ - t * threeDForcingAmplitude θ) ^ 2) =
        threeDWeightedMass r s -
          (2 * t) * originalGCIDenominator 3 r s +
          t ^ 2 * originalForcingNorm 3 r := by
    rw [threeDWeightedMass,
      threeD_denominator_mass_formula r s hs.1,
      threeD_forcingNorm_mass_formula]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
            (Real.exp (r * Real.cos θ) * (momentPrimitive s θ) ^ 2 -
              (2 * t) * (Real.exp (r * Real.cos θ) *
                threeDForcingAmplitude θ * momentPrimitive s θ)) +
              t ^ 2 * (Real.exp (r * Real.cos θ) *
                (threeDForcingAmplitude θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
            (hM.sub (hD.const_mul (2 * t)))
            (hZ.const_mul (t ^ 2)),
          intervalIntegral.integral_sub hM (hD.const_mul (2 * t)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hqexp] at hqnonneg
  have ht2 : t ^ 2 * originalForcingNorm 3 r =
      t * originalGCIDenominator 3 r s := by
    calc
      _ = t * (t * originalForcingNorm 3 r) := by ring
      _ = t * originalGCIDenominator 3 r s := by rw [ht]
  have hMD : t * originalGCIDenominator 3 r s ≤
      threeDWeightedMass r s := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hMD hZpos.le
  have hprod : t * originalGCIDenominator 3 r s *
      originalForcingNorm 3 r =
        (originalGCIDenominator 3 r s) ^ 2 := by
    calc
      _ = (t * originalForcingNorm 3 r) *
            originalGCIDenominator 3 r s := by ring
      _ = (originalGCIDenominator 3 r s) ^ 2 := by
        rw [ht]
        ring
  nlinarith

end

end DFL.GCI
