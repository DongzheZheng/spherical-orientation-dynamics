import DFL.GCI.AngularSineTest

/-!
# Exact forcing moment in ambient dimension two

The case `n=2` has no singular angular potential, and the original
weighted `H¹₀` representative is `g` itself.  This permits a direct
absolutely continuous integration by parts within the original weak
form, with no assumed classical regularity of the solution.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def twoDPrimitive (s : AngularState) (θ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..θ, s.scaledDerivative u

theorem twoD_reconstruction (s : AngularState)
    (hs : AngularEnergyDomain 2 s)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    s.g θ = twoDPrimitive s θ := by
  simpa [scaledFunction, halfPower, twoDPrimitive]
    using hs.2.2.1 θ hθ

theorem twoDPrimitive_AC (s : AngularState)
    (hs : AngularEnergyDomain 2 s) :
    AbsolutelyContinuousOnInterval (twoDPrimitive s)
      (0 : ℝ) Real.pi := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  exact hs.1.absolutelyContinuousOnInterval_intervalIntegral h0

theorem twoD_g_continuousOn (s : AngularState)
    (hs : AngularEnergyDomain 2 s) :
    ContinuousOn s.g (Set.Icc (0 : ℝ) Real.pi) := by
  have hprim := (twoDPrimitive_AC s hs).continuousOn
  have hprimIcc : ContinuousOn (twoDPrimitive s)
      (Set.Icc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hprim
  apply hprimIcc.congr
  intro θ hθ
  exact twoD_reconstruction s hs θ hθ

theorem twoD_angularDerivative (s : AngularState) (θ : ℝ) :
    angularDerivative 2 s θ = s.scaledDerivative θ := by
  simp [angularDerivative, halfPower]

theorem twoD_angularWeight (r θ : ℝ) :
    angularWeight 2 r θ = Real.exp (r * Real.cos θ) := by
  simp [angularWeight]

private theorem twoD_angularPotential (θ : ℝ) :
    angularPotential 2 θ = 0 := by
  simp [angularPotential]

private def twoDFluxWeight (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * Real.cos θ

private theorem twoDFluxWeight_hasDerivAt (r θ : ℝ) :
    HasDerivAt (twoDFluxWeight r)
      (-(Real.exp (r * Real.cos θ) *
          Real.sin θ * (1 + r * Real.cos θ))) θ := by
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  have hexp := harg.exp
  have hprod := hexp.mul (Real.hasDerivAt_cos θ)
  convert hprod using 1
  ring

private theorem twoDFluxWeight_AC (r : ℝ) :
    AbsolutelyContinuousOnInterval (twoDFluxWeight r)
      (0 : ℝ) Real.pi := by
  have hC1 : ContDiff ℝ 1 (twoDFluxWeight r) := by
    unfold twoDFluxWeight
    fun_prop
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKu : LipschitzOnWith K (twoDFluxWeight r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  exact hKu.absolutelyContinuousOnInterval

private theorem twoD_integral_ibp
    (s : AngularState) (hs : AngularEnergyDomain 2 s) (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        twoDFluxWeight r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * Real.sin θ *
          (1 + r * Real.cos θ) * s.g θ := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  have huAC : AbsolutelyContinuousOnInterval
      (twoDPrimitive s) (0 : ℝ) Real.pi :=
    hs.1.absolutelyContinuousOnInterval_intervalIntegral h0
  have hqae := hs.1.ae_hasDerivAt_integral
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        twoDFluxWeight r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        twoDFluxWeight r θ * deriv (twoDPrimitive s) θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with θ hq hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hθIoc.1.le, hθIoc.2⟩
    have hderiv :
        deriv (twoDPrimitive s) θ = s.scaledDerivative θ := by
      exact (hq hθ' 0 h0).deriv
    rw [hderiv]
  have hu0 : twoDPrimitive s 0 = 0 := by
    simp [twoDPrimitive]
  have huπ : twoDPrimitive s Real.pi = 0 :=
    hs.2.2.2.1
  have hFderiv (θ : ℝ) :
      deriv (twoDFluxWeight r) θ =
        -(Real.exp (r * Real.cos θ) *
            Real.sin θ * (1 + r * Real.cos θ)) :=
    (twoDFluxWeight_hasDerivAt r θ).deriv
  have hIBP := (twoDFluxWeight_AC r).integral_mul_deriv_eq_deriv_mul huAC
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          twoDFluxWeight r θ * deriv (twoDPrimitive s) θ := hleft
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
          deriv (twoDFluxWeight r) θ * twoDPrimitive s θ) := by
      simpa [hu0, huπ] using hIBP
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          -(deriv (twoDFluxWeight r) θ * twoDPrimitive s θ) := by
      rw [intervalIntegral.integral_neg]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) * Real.sin θ *
            (1 + r * Real.cos θ) * s.g θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [hFderiv, ← twoD_reconstruction s hs θ hθIcc]
      ring

theorem twoD_denominator_formula (r : ℝ) (s : AngularState) :
    originalGCIDenominator 2 r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ := by
  unfold originalGCIDenominator
  apply intervalIntegral.integral_congr
  intro θ _
  norm_num
  ring

theorem twoD_numerator_formula (r : ℝ) (s : AngularState) :
    originalGCINumerator 2 r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.cos θ *
          (Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ) := by
  unfold originalGCINumerator
  apply intervalIntegral.integral_congr
  intro θ _
  norm_num
  ring

theorem twoD_weakForm_sine
    (r : ℝ) (s : AngularState) :
    originalWeakForm 2 r s (sineTestState 2) =
      ∫ θ in (0 : ℝ)..Real.pi,
        twoDFluxWeight r θ * s.scaledDerivative θ := by
  unfold originalWeakForm
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [twoD_angularWeight, twoD_angularDerivative,
    twoD_angularPotential]
  have ht : angularDerivative 2 (sineTestState 2) θ =
      Real.cos θ := by
    simp [twoD_angularDerivative, sineTestState, sineTestQ]
  rw [ht]
  simp [twoDFluxWeight]
  ring

/-- Exact moment identity for the *original weak GCI solution* in ambient
dimension two: the forcing norm is the denominator plus the field times
the numerator.  No smoothness or sign hypothesis is added to the weak
solution.  For higher dimensions the weighted endpoint integration by
parts is a separate source-space obligation. -/
theorem weak_solution_moment_identity_twoD
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    originalForcingNorm 2 r =
      originalGCIDenominator 2 r s +
        r * originalGCINumerator 2 r s := by
  have htest : AngularEnergyDomain 2 (sineTestState 2) :=
    sineTestState_mem_energy 2 (by omega)
  have hweak := (hs.2 (sineTestState 2) htest).2.2
  rw [sourcePairing_sine_eq_forcingNorm,
    twoD_weakForm_sine] at hweak
  have hIBP := twoD_integral_ibp s hs.1 r
  have hD : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ)
      volume (0 : ℝ) Real.pi := by
    simpa only [twoD_angularWeight] using (hs.2 s hs.1).2.1
  have hN : IntervalIntegrable
      (fun θ : ℝ =>
        Real.cos θ *
          (Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ))
      volume (0 : ℝ) Real.pi :=
    hD.continuousOn_mul Real.continuous_cos.continuousOn
  calc
    originalForcingNorm 2 r =
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) * Real.sin θ *
            (1 + r * Real.cos θ) * s.g θ := by
      rw [← hIBP]
      exact hweak.symm
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ) +
        r * (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos θ *
            (Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ)) := by
      calc
        _ = ∫ θ in (0 : ℝ)..Real.pi,
              (Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ) +
                r * (Real.cos θ *
                  (Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ)) := by
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add hD (hN.const_mul r),
            intervalIntegral.integral_const_mul]
    _ = originalGCIDenominator 2 r s +
        r * originalGCINumerator 2 r s := by
      rw [twoD_denominator_formula, twoD_numerator_formula]

/-- In the original two-dimensional weak problem, positivity of the GCI
numerator is exactly the strict spectral response bound `D < Z`.
This isolates the analytic inequality still needed for this part of the
historical conjecture, without assuming either side. -/
theorem weak_solution_numerator_pos_iff_twoD
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    0 < originalGCINumerator 2 r s ↔
      originalGCIDenominator 2 r s < originalForcingNorm 2 r := by
  have hm := weak_solution_moment_identity_twoD r s hs
  constructor
  · intro hN
    have hprod := mul_pos hr hN
    linarith
  · intro hDZ
    have hprod : 0 < r * originalGCINumerator 2 r s := by
      linarith
    nlinarith

end

end DFL.GCI
