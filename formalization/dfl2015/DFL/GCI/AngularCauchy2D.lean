import DFL.GCI.AngularBarrier2D

/-!
# Weighted angular Cauchy inequality for the original two-dimensional weak solution

This is a direct quadratic-form proof on the original angular interval.
The mass integral is finite because in ambient dimension two the
represented weak solution has an absolutely continuous representative.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def twoDMass (r : ℝ) (s : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (r * Real.cos θ) * (s.g θ) ^ 2

theorem twoD_forcingNorm_formula (r : ℝ) :
    originalForcingNorm 2 r =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 := by
  unfold originalForcingNorm
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [twoD_angularWeight]

/-- Finiteness of the original weighted `L²` mass in ambient dimension
two follows directly from the AC representative of the source domain. -/
theorem twoDMass_integrable
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 2 s) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (s.g θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  have hw : ContinuousOn (fun θ : ℝ => Real.exp (r * Real.cos θ))
      (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ))).continuousOn
  have hg := twoD_g_continuousOn s hs
  exact (hw.mul (hg.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le

/-- A finite-interval Cauchy inequality involving the *original*
denominator, the forcing norm, and the actual weak solution mass.
No auxiliary amplitude or sign hypothesis appears. -/
theorem weak_solution_weighted_cauchy_twoD
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    (originalGCIDenominator 2 r s) ^ 2 ≤
      originalForcingNorm 2 r * twoDMass r s := by
  have hZpos : 0 < originalForcingNorm 2 r :=
    originalForcingNorm_pos_of_weak_solution 2 (by omega) r s hs
  have hM : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (s.g θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    twoDMass_integrable r s hs.1
  have hD : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ)
      volume (0 : ℝ) Real.pi := by
    simpa only [twoD_angularWeight] using (hs.2 s hs.1).2.1
  have hZ : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)).intervalIntegrable _ _
  let t : ℝ := originalGCIDenominator 2 r s / originalForcingNorm 2 r
  have ht : t * originalForcingNorm 2 r =
      originalGCIDenominator 2 r s := by
    dsimp [t]
    exact div_mul_cancel₀ _ hZpos.ne'
  have hqnonneg :
      0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (s.g θ - t * Real.sin θ) ^ 2 := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hqexp :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (s.g θ - t * Real.sin θ) ^ 2) =
        twoDMass r s -
          (2 * t) * originalGCIDenominator 2 r s +
          t ^ 2 * originalForcingNorm 2 r := by
    rw [twoDMass, twoD_denominator_formula, twoD_forcingNorm_formula]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
            (Real.exp (r * Real.cos θ) * (s.g θ) ^ 2 -
              (2 * t) *
                (Real.exp (r * Real.cos θ) *
                  Real.sin θ * s.g θ)) +
              t ^ 2 *
                (Real.exp (r * Real.cos θ) *
                  (Real.sin θ) ^ 2) := by
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
  have ht2 : t ^ 2 * originalForcingNorm 2 r =
      t * originalGCIDenominator 2 r s := by
    calc
      _ = t * (t * originalForcingNorm 2 r) := by ring
      _ = t * originalGCIDenominator 2 r s := by rw [ht]
  have hMD : t * originalGCIDenominator 2 r s ≤ twoDMass r s := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hMD hZpos.le
  have hprod : t * originalGCIDenominator 2 r s *
      originalForcingNorm 2 r =
        (originalGCIDenominator 2 r s) ^ 2 := by
    calc
      _ = (t * originalForcingNorm 2 r) *
            originalGCIDenominator 2 r s := by ring
      _ = (originalGCIDenominator 2 r s) ^ 2 := by
        rw [ht]
        ring
  nlinarith

end

end DFL.GCI
