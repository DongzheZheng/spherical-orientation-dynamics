import DFL.GCI.AngularSpectral2D

/-!
# Original two-dimensional GCI upper comparison

The original bilinear form gives an energy Cauchy inequality between the
actual weak solution and the physical sine test.  This will compare the
GCI coefficient with the dimension-shifted orientation mean, without
requiring pointwise monotonicity of an auxiliary amplitude.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def twoDSineEnergy (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2

def twoDShiftMoment (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (r * Real.cos θ) *
      Real.cos θ * (Real.sin θ) ^ 2

theorem twoDSineEnergy_pos (r : ℝ) :
    0 < twoDSineEnergy r := by
  unfold twoDSineEnergy
  have hc : ContinuousOn
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2)
      (Set.Icc (0 : ℝ) Real.pi) := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2)).continuousOn
  apply intervalIntegral.integral_pos Real.pi_pos hc
  · intro θ _
    exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  · refine ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, ?_⟩
    simpa using Real.exp_pos r

private def twoDShiftFlux (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * Real.sin θ * Real.cos θ

private theorem twoDShiftFlux_hasDerivAt (r θ : ℝ) :
    HasDerivAt (twoDShiftFlux r)
      (Real.exp (r * Real.cos θ) *
        ((Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 -
          r * (Real.sin θ) ^ 2 * Real.cos θ)) θ := by
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  have hprod := ((harg.exp.mul (Real.hasDerivAt_sin θ)).mul
    (Real.hasDerivAt_cos θ))
  convert hprod using 1
  simp only [Pi.mul_apply]
  ring

private theorem twoDShiftFlux_integral_zero (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos θ) *
        ((Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 -
          r * (Real.sin θ) ^ 2 * Real.cos θ)) = 0 := by
  have hcont : ContinuousOn (twoDShiftFlux r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    exact (by unfold twoDShiftFlux; fun_prop :
      Continuous (twoDShiftFlux r)).continuousOn
  have hint : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) *
          ((Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 -
            r * (Real.sin θ) ^ 2 * Real.cos θ))
      volume (0 : ℝ) Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) *
        ((Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 -
          r * (Real.sin θ) ^ 2 * Real.cos θ))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    Real.pi_pos.le hcont
    (fun θ _ => twoDShiftFlux_hasDerivAt r θ) hint
  simpa [twoDShiftFlux, Real.sin_zero, Real.sin_pi] using hFTC

/-- Applying the original angular operator to `sin θ` and integrating
the smooth flux gives `T=Z+rC`, with no weak-solution assumptions. -/
theorem twoDSineEnergy_eq_forcingNorm_add_shiftMoment (r : ℝ) :
    twoDSineEnergy r =
      originalForcingNorm 2 r + r * twoDShiftMoment r := by
  have hE : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2)).intervalIntegrable _ _
  have hZ : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)).intervalIntegrable _ _
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) *
          Real.cos θ * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) *
        Real.cos θ * (Real.sin θ) ^ 2)).intervalIntegrable _ _
  have hzero := twoDShiftFlux_integral_zero r
  have hlinear :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          ((Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 -
            r * (Real.sin θ) ^ 2 * Real.cos θ)) =
      twoDSineEnergy r - originalForcingNorm 2 r -
        r * twoDShiftMoment r := by
    rw [twoDSineEnergy, twoDShiftMoment,
      twoD_forcingNorm_formula]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
            (Real.exp (r * Real.cos θ) *
              (Real.cos θ) ^ 2 -
              Real.exp (r * Real.cos θ) *
                (Real.sin θ) ^ 2) -
              r * (Real.exp (r * Real.cos θ) *
                Real.cos θ * (Real.sin θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hE.sub hZ)
            (hC.const_mul r),
          intervalIntegral.integral_sub hE hZ,
          intervalIntegral.integral_const_mul]
  linarith

private theorem twoD_sineDerivative (θ : ℝ) :
    angularDerivative 2 (sineTestState 2) θ = Real.cos θ := by
  simp [twoD_angularDerivative, sineTestState, sineTestQ]

/-- The original weak equation gives a weighted energy Cauchy bound
against the physical sine test.  The derivative of that test is `cos θ`;
all three energy integrals are supplied by the original weak domain. -/
theorem weak_solution_energy_cauchy_twoD
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    (originalForcingNorm 2 r) ^ 2 ≤
      originalGCIDenominator 2 r s * twoDSineEnergy r := by
  let q := s.scaledDerivative
  let W := fun θ : ℝ => Real.exp (r * Real.cos θ)
  have htest : AngularEnergyDomain 2 (sineTestState 2) :=
    sineTestState_mem_energy 2 (by omega)
  have hEraw := (hs.2 s hs.1).1
  have hCrossRaw := (hs.2 (sineTestState 2) htest).1
  have hE : IntervalIntegrable
      (fun θ : ℝ => W θ * (q θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply hEraw.congr
    intro θ _
    dsimp only [W, q]
    rw [twoD_angularWeight, twoD_angularDerivative]
    simp [angularPotential]
    ring
  have hCross : IntervalIntegrable
      (fun θ : ℝ => W θ * q θ * Real.cos θ)
      volume (0 : ℝ) Real.pi := by
    apply hCrossRaw.congr
    intro θ _
    dsimp only [W, q]
    rw [twoD_angularWeight, twoD_angularDerivative,
      twoD_sineDerivative]
    simp [angularPotential]
    ring
  have hT : IntervalIntegrable
      (fun θ : ℝ => W θ * (Real.cos θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    exact (by dsimp [W]; fun_prop : Continuous (fun θ : ℝ =>
      W θ * (Real.cos θ) ^ 2)).intervalIntegrable _ _
  have hEeq :
      (∫ θ in (0 : ℝ)..Real.pi, W θ * (q θ) ^ 2) =
        originalGCIDenominator 2 r s := by
    calc
      _ = originalWeakForm 2 r s s := (twoD_energy_formula r s).symm
      _ = originalSourcePairing 2 r s := (hs.2 s hs.1).2.2
      _ = originalGCIDenominator 2 r s :=
        originalSourcePairing_eq_denominator 2 (by omega) r s
  have hCrossEq :
      (∫ θ in (0 : ℝ)..Real.pi,
          W θ * q θ * Real.cos θ) =
        originalForcingNorm 2 r := by
    calc
      _ = originalWeakForm 2 r s (sineTestState 2) := by
        unfold originalWeakForm
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only [W, q]
        rw [twoD_angularWeight, twoD_angularDerivative,
          twoD_sineDerivative]
        simp [angularPotential]
        ring
      _ = originalSourcePairing 2 r (sineTestState 2) :=
        (hs.2 (sineTestState 2) htest).2.2
      _ = originalForcingNorm 2 r :=
        sourcePairing_sine_eq_forcingNorm 2 r
  have hTpos : 0 < twoDSineEnergy r := twoDSineEnergy_pos r
  let t : ℝ := originalForcingNorm 2 r / twoDSineEnergy r
  have ht : t * twoDSineEnergy r = originalForcingNorm 2 r := by
    dsimp [t]
    exact div_mul_cancel₀ _ hTpos.ne'
  have hqnonneg :
      0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
        W θ * (q θ - t * Real.cos θ) ^ 2 := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hqexp :
      (∫ θ in (0 : ℝ)..Real.pi,
        W θ * (q θ - t * Real.cos θ) ^ 2) =
        originalGCIDenominator 2 r s -
          (2 * t) * originalForcingNorm 2 r +
          t ^ 2 * twoDSineEnergy r := by
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
            (hE.sub (hCross.const_mul (2 * t)))
            (hT.const_mul (t ^ 2)),
          intervalIntegral.integral_sub hE
            (hCross.const_mul (2 * t)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          hEeq, hCrossEq]
        rfl
  rw [hqexp] at hqnonneg
  have ht2 : t ^ 2 * twoDSineEnergy r =
      t * originalForcingNorm 2 r := by
    calc
      _ = t * (t * twoDSineEnergy r) := by ring
      _ = t * originalForcingNorm 2 r := by rw [ht]
  have hZD : t * originalForcingNorm 2 r ≤
      originalGCIDenominator 2 r s := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hZD hTpos.le
  have hprod : t * originalForcingNorm 2 r * twoDSineEnergy r =
      (originalForcingNorm 2 r) ^ 2 := by
    calc
      _ = (t * twoDSineEnergy r) * originalForcingNorm 2 r := by ring
      _ = (originalForcingNorm 2 r) ^ 2 := by rw [ht]; ring
  nlinarith

/-- A direct original-coefficient bound by the dimension-shifted
first moment, before identifying that moment with `c₄(r)`. -/
theorem weak_solution_coefficient_le_shift_moment_twoD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    originalGCICoefficient 2 r s ≤
      twoDShiftMoment r / originalForcingNorm 2 r := by
  have hD := weak_solution_denominator_pos 2 (by omega) r s hs
  have hZ := originalForcingNorm_pos_of_weak_solution
    2 (by omega) r s hs
  have hC := weak_solution_energy_cauchy_twoD r s hs
  have hT := twoDSineEnergy_eq_forcingNorm_add_shiftMoment r
  have hM := weak_solution_moment_identity_twoD r s hs
  have hND : originalForcingNorm 2 r *
      originalGCINumerator 2 r s ≤
      originalGCIDenominator 2 r s * twoDShiftMoment r := by
    nlinarith [mul_nonneg hr.le hZ.le]
  unfold originalGCICoefficient
  exact (div_le_div_iff₀ hD hZ).2 (by nlinarith [hND])

end

end DFL.GCI
