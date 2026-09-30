import DFL.GCI.AngularMomentThree

/-!
# Weak-solution integrability for the ambient dimension three moment

These statements use only the original represented weak equation.  The
singular remainder is shown integrable by subtracting the regular flux
term from the integrable original weak-form density, rather than by
prescribing its endpoint behavior.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

theorem threeD_momentFlux_continuous (r : ℝ) :
    Continuous (momentFlux 3 r) := by
  have hp : Continuous
      (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower 3)) :=
    (Real.continuous_rpow_const (by norm_num [halfPower] :
      (0 : ℝ) ≤ halfPower 3)).comp Real.continuous_sin
  unfold momentFlux
  fun_prop

theorem threeD_momentDenominatorWeight_continuous (r : ℝ) :
    Continuous (momentDenominatorWeight 3 r) := by
  have hp : Continuous
      (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower 3 + 1)) :=
    (Real.continuous_rpow_const (by norm_num [halfPower] :
      (0 : ℝ) ≤ halfPower 3 + 1)).comp Real.continuous_sin
  unfold momentDenominatorWeight
  fun_prop

theorem threeD_flux_derivative_term_integrable
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 3 s) :
    IntervalIntegrable
      (fun θ : ℝ => momentFlux 3 r θ * s.scaledDerivative θ)
      volume (0 : ℝ) Real.pi := by
  have hFcont : ContinuousOn (momentFlux 3 r)
      (Set.uIcc (0 : ℝ) Real.pi) :=
    (threeD_momentFlux_continuous r).continuousOn
  simpa only [mul_comm] using hs.1.continuousOn_mul hFcont

theorem threeD_remainder_integrable
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s) :
    IntervalIntegrable
      (fun θ : ℝ => momentRemainderWeight 3 r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
  have htest : AngularEnergyDomain 3 (sineTestState 3) :=
    sineTestState_mem_energy 3 (by omega)
  have hWeak := (hs.2 (sineTestState 3) htest).1
  have hFq := threeD_flux_derivative_term_integrable r s hs.1
  have hSum : IntervalIntegrable
      (fun θ : ℝ => momentFlux 3 r θ * s.scaledDerivative θ +
        momentRemainderWeight 3 r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
    apply hWeak.congr_ae
    filter_upwards [moment_ae_interior] with θ hθ
    exact moment_weakForm_sine_density 3 r s hs.1 θ hθ
  have hDiff := hSum.sub hFq
  convert hDiff using 1
  funext θ
  ring

theorem threeD_ibp_term_integrable
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s) :
    IntervalIntegrable
      (fun θ : ℝ => momentIBPWeight 3 r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
  have hu := momentPrimitive_continuousOn 3 s hs.1
  have hM : IntervalIntegrable
      (fun θ : ℝ => momentDenominatorWeight 3 r θ *
        (((3 : ℝ) - 1) + r * Real.cos θ) * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
    have hc : ContinuousOn
        (fun θ : ℝ => momentDenominatorWeight 3 r θ *
          (((3 : ℝ) - 1) + r * Real.cos θ))
        (Set.Icc (0 : ℝ) Real.pi) := by
      exact (threeD_momentDenominatorWeight_continuous r).continuousOn.mul
        (by fun_prop : ContinuousOn
          (fun θ : ℝ => (((3 : ℝ) - 1) + r * Real.cos θ))
          (Set.Icc (0 : ℝ) Real.pi))
    exact (hc.mul hu).intervalIntegrable_of_Icc Real.pi_pos.le
  have hR := threeD_remainder_integrable r s hs
  have hDiff := hM.sub hR
  apply hDiff.congr_ae
  filter_upwards [moment_ae_interior] with θ hθ
  have hDensity := moment_moment_density 3 r θ (momentPrimitive s θ) hθ
  norm_num only [Nat.cast_ofNat] at hDensity
  linarith [hDensity]

theorem threeD_weakForm_sine
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s) :
    originalWeakForm 3 r s (sineTestState 3) =
      (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux 3 r θ * s.scaledDerivative θ) +
      (∫ θ in (0 : ℝ)..Real.pi,
        momentRemainderWeight 3 r θ * momentPrimitive s θ) := by
  have hFq := threeD_flux_derivative_term_integrable r s hs.1
  have hR := threeD_remainder_integrable r s hs
  calc
    originalWeakForm 3 r s (sineTestState 3) =
        ∫ θ in (0 : ℝ)..Real.pi,
          momentFlux 3 r θ * s.scaledDerivative θ +
            momentRemainderWeight 3 r θ * momentPrimitive s θ := by
      unfold originalWeakForm
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      exact moment_weakForm_sine_density 3 r s hs.1 θ hθ
    _ = _ := intervalIntegral.integral_add hFq hR

theorem threeD_integral_ibp_of_flux_AC
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s)
    (hFluxAC : AbsolutelyContinuousOnInterval
      (momentFlux 3 r) (0 : ℝ) Real.pi) :
    (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux 3 r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        momentIBPWeight 3 r θ * momentPrimitive s θ := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  have huAC := momentPrimitive_AC 3 s hs.1
  have hqae := hs.1.1.ae_hasDerivAt_integral
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux 3 r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        momentFlux 3 r θ * deriv (momentPrimitive s) θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with θ hq hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hθIoc.1.le, hθIoc.2⟩
    have hderiv :
        deriv (momentPrimitive s) θ = s.scaledDerivative θ := by
      exact (hq hθ' 0 h0).deriv
    rw [hderiv]
  have hu0 : momentPrimitive s 0 = 0 := by
    simp [momentPrimitive]
  have huπ : momentPrimitive s Real.pi = 0 := hs.1.2.2.2.1
  have hIBP := hFluxAC.integral_mul_deriv_eq_deriv_mul huAC
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentFlux 3 r θ * deriv (momentPrimitive s) θ := hleft
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
          deriv (momentFlux 3 r) θ * momentPrimitive s θ) := by
      simpa [hu0, huπ] using hIBP
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          -(deriv (momentFlux 3 r) θ * momentPrimitive s θ) := by
      rw [intervalIntegral.integral_neg]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentIBPWeight 3 r θ * momentPrimitive s θ := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      rw [(momentFlux_hasDerivAt 3 r θ hθ).deriv]
      ring

/-- The original dimension-three weak moment follows from the analytic
endpoint regularity of its explicit `√sin` flux.  The latter is an
independent function-theoretic statement, not a hypothesis about the
solution, coefficient, or desired comparison. -/
theorem weak_solution_moment_identity_three_of_flux_AC
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s)
    (hFluxAC : AbsolutelyContinuousOnInterval
      (momentFlux 3 r) (0 : ℝ) Real.pi) :
    originalForcingNorm 3 r =
      2 * originalGCIDenominator 3 r s +
        r * originalGCINumerator 3 r s := by
  have htest : AngularEnergyDomain 3 (sineTestState 3) :=
    sineTestState_mem_energy 3 (by omega)
  have hweak := (hs.2 (sineTestState 3) htest).2.2
  rw [sourcePairing_sine_eq_forcingNorm] at hweak
  have hIBP := threeD_integral_ibp_of_flux_AC r s hs hFluxAC
  have hB := threeD_ibp_term_integrable r s hs
  have hR := threeD_remainder_integrable r s hs
  have hu := momentPrimitive_continuousOn 3 s hs.1
  have hD : IntervalIntegrable
      (fun θ : ℝ => momentDenominatorWeight 3 r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (((threeD_momentDenominatorWeight_continuous r).continuousOn).mul hu).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hN : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ * momentDenominatorWeight 3 r θ *
        momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
    exact (hD.continuousOn_mul Real.continuous_cos.continuousOn).congr
      (by intro θ _; ring)
  calc
    originalForcingNorm 3 r =
        originalWeakForm 3 r s (sineTestState 3) := hweak.symm
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          momentFlux 3 r θ * s.scaledDerivative θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          momentRemainderWeight 3 r θ * momentPrimitive s θ) :=
      threeD_weakForm_sine r s hs
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          momentIBPWeight 3 r θ * momentPrimitive s θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          momentRemainderWeight 3 r θ * momentPrimitive s θ) := by
      rw [hIBP]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentDenominatorWeight 3 r θ *
            (((3 : ℝ) - 1) + r * Real.cos θ) * momentPrimitive s θ := by
      rw [← intervalIntegral.integral_add hB hR]
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      exact moment_moment_density 3 r θ (momentPrimitive s θ) hθ
    _ = 2 * originalGCIDenominator 3 r s +
        r * originalGCINumerator 3 r s := by
      rw [moment_denominator_formula 3 r s hs.1,
        moment_numerator_formula 3 r s hs.1]
      calc
        _ = ∫ θ in (0 : ℝ)..Real.pi,
              2 * (momentDenominatorWeight 3 r θ * momentPrimitive s θ) +
              r * (Real.cos θ * momentDenominatorWeight 3 r θ *
                momentPrimitive s θ) := by
          apply intervalIntegral.integral_congr
          intro θ _
          norm_num
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add (hD.const_mul 2)
            (hN.const_mul r),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]

end

end DFL.GCI
