import DFL.GCI.AngularEnergyCauchy

/-!
# Exact original weak forcing moment in ambient dimension four

For `n=4`, the represented weighted `H¹₀` function is
`u(θ)=sin θ*g(θ)`.  Its absolutely continuous representative permits
integration by parts against the physical sine test without assuming that
the original weak solution is classically differentiable.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def fourDPrimitive (s : AngularState) (θ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..θ, s.scaledDerivative u

theorem fourD_reconstruction (s : AngularState)
    (hs : AngularEnergyDomain 4 s)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    Real.sin θ * s.g θ = fourDPrimitive s θ := by
  have h := hs.2.2.1 θ hθ
  norm_num [scaledFunction, halfPower, fourDPrimitive] at h ⊢
  exact h

theorem fourDPrimitive_AC (s : AngularState)
    (hs : AngularEnergyDomain 4 s) :
    AbsolutelyContinuousOnInterval (fourDPrimitive s)
      (0 : ℝ) Real.pi := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  exact hs.1.absolutelyContinuousOnInterval_intervalIntegral h0

theorem fourDPrimitive_continuousOn (s : AngularState)
    (hs : AngularEnergyDomain 4 s) :
    ContinuousOn (fourDPrimitive s) (Set.Icc (0 : ℝ) Real.pi) := by
  simpa only [Set.uIcc_of_le Real.pi_pos.le] using
    (fourDPrimitive_AC s hs).continuousOn

private def fourDFluxWeight (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * Real.sin θ * Real.cos θ

private def fourDIBPWeight (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    ((Real.sin θ) ^ 2 - (Real.cos θ) ^ 2 +
      r * (Real.sin θ) ^ 2 * Real.cos θ)

private def fourDRemainderWeight (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * (2 - (Real.cos θ) ^ 2)

private theorem fourDFluxWeight_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fourDFluxWeight r)
      (-fourDIBPWeight r θ) θ := by
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  have hexp := harg.exp
  have hprod := (hexp.mul (Real.hasDerivAt_sin θ)).mul
    (Real.hasDerivAt_cos θ)
  convert hprod using 1
  simp [fourDIBPWeight]
  ring

private theorem fourDFluxWeight_AC (r : ℝ) :
    AbsolutelyContinuousOnInterval (fourDFluxWeight r)
      (0 : ℝ) Real.pi := by
  have hC1 : ContDiff ℝ 1 (fourDFluxWeight r) := by
    unfold fourDFluxWeight
    fun_prop
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKu : LipschitzOnWith K (fourDFluxWeight r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  exact hKu.absolutelyContinuousOnInterval

private theorem fourD_integral_ibp
    (s : AngularState) (hs : AngularEnergyDomain 4 s) (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        fourDFluxWeight r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        fourDIBPWeight r θ * fourDPrimitive s θ := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  have huAC : AbsolutelyContinuousOnInterval
      (fourDPrimitive s) (0 : ℝ) Real.pi :=
    fourDPrimitive_AC s hs
  have hqae := hs.1.ae_hasDerivAt_integral
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        fourDFluxWeight r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        fourDFluxWeight r θ * deriv (fourDPrimitive s) θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with θ hq hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hθIoc.1.le, hθIoc.2⟩
    have hderiv :
        deriv (fourDPrimitive s) θ = s.scaledDerivative θ := by
      exact (hq hθ' 0 h0).deriv
    rw [hderiv]
  have hu0 : fourDPrimitive s 0 = 0 := by
    simp [fourDPrimitive]
  have huπ : fourDPrimitive s Real.pi = 0 := hs.2.2.2.1
  have hFderiv (θ : ℝ) :
      deriv (fourDFluxWeight r) θ =
        -fourDIBPWeight r θ :=
    (fourDFluxWeight_hasDerivAt r θ).deriv
  have hIBP := (fourDFluxWeight_AC r).integral_mul_deriv_eq_deriv_mul huAC
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          fourDFluxWeight r θ * deriv (fourDPrimitive s) θ := hleft
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
          deriv (fourDFluxWeight r) θ * fourDPrimitive s θ) := by
      simpa [hu0, huπ] using hIBP
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          -(deriv (fourDFluxWeight r) θ * fourDPrimitive s θ) := by
      rw [intervalIntegral.integral_neg]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          fourDIBPWeight r θ * fourDPrimitive s θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hFderiv]
      ring

private theorem fourD_ae_interior :
    ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
      θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hmem :
      ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
        θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa only [Set.uIoc_of_le Real.pi_pos.le] using
      (ae_restrict_mem (μ := volume) measurableSet_Ioc)
  have hne :
      ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
        θ ≠ Real.pi :=
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne Real.pi)
  filter_upwards [hmem, hne] with θ hθ hθne
  exact ⟨hθ.1, lt_of_le_of_ne hθ.2 hθne⟩

private theorem fourD_weakForm_sine_density
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 4 s)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularWeight 4 r θ *
      (angularDerivative 4 s θ *
          angularDerivative 4 (sineTestState 4) θ +
        angularPotential 4 θ * s.g θ * (sineTestState 4).g θ) =
      fourDFluxWeight r θ * s.scaledDerivative θ +
        fourDRemainderWeight r θ * fourDPrimitive s θ := by
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo hθ).ne'
  have hrec : fourDPrimitive s θ = Real.sin θ * s.g θ :=
    (fourD_reconstruction s hs θ ⟨hθ.1.le, hθ.2.le⟩).symm
  rw [sineTest_angularDerivative_interior 4 θ hθ, hrec]
  norm_num [angularWeight, angularDerivative, angularPotential,
    halfPower, sineTestState, fourDFluxWeight, fourDRemainderWeight]
  field_simp [hsin]
  ring

private theorem fourD_weakForm_sine
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 4 r s) :
    originalWeakForm 4 r s (sineTestState 4) =
      (∫ θ in (0 : ℝ)..Real.pi,
        fourDFluxWeight r θ * s.scaledDerivative θ) +
      (∫ θ in (0 : ℝ)..Real.pi,
        fourDRemainderWeight r θ * fourDPrimitive s θ) := by
  have hFcont : ContinuousOn (fourDFluxWeight r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    unfold fourDFluxWeight
    fun_prop
  have hFq : IntervalIntegrable
      (fun θ : ℝ => fourDFluxWeight r θ * s.scaledDerivative θ)
      volume (0 : ℝ) Real.pi := by
    simpa only [mul_comm] using hs.1.1.continuousOn_mul hFcont
  have hRcont : ContinuousOn (fourDRemainderWeight r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    unfold fourDRemainderWeight
    fun_prop
  have hR : IntervalIntegrable
      (fun θ : ℝ => fourDRemainderWeight r θ * fourDPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (hRcont.mul (fourDPrimitive_continuousOn s hs.1)).intervalIntegrable_of_Icc
      Real.pi_pos.le
  calc
    originalWeakForm 4 r s (sineTestState 4) =
        ∫ θ in (0 : ℝ)..Real.pi,
          fourDFluxWeight r θ * s.scaledDerivative θ +
            fourDRemainderWeight r θ * fourDPrimitive s θ := by
      unfold originalWeakForm
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [fourD_ae_interior] with θ hθ
      exact fourD_weakForm_sine_density r s hs.1 θ hθ
    _ = _ := intervalIntegral.integral_add hFq hR

private theorem fourD_moment_density (r θ u : ℝ) :
    fourDIBPWeight r θ * u + fourDRemainderWeight r θ * u =
      Real.exp (r * Real.cos θ) *
        (Real.sin θ) ^ 2 * (3 + r * Real.cos θ) * u := by
  have ht := Real.sin_sq_add_cos_sq θ
  have hcore :
      (Real.sin θ) ^ 2 - (Real.cos θ) ^ 2 +
          (2 - (Real.cos θ) ^ 2) =
        3 * (Real.sin θ) ^ 2 := by
    nlinarith
  dsimp [fourDIBPWeight, fourDRemainderWeight]
  calc
    _ = Real.exp (r * Real.cos θ) *
          ((Real.sin θ) ^ 2 - (Real.cos θ) ^ 2 +
            (2 - (Real.cos θ) ^ 2) +
            r * (Real.sin θ) ^ 2 * Real.cos θ) * u := by ring
    _ = _ := by rw [hcore]; ring

theorem fourD_denominator_formula
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 4 s) :
    originalGCIDenominator 4 r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) *
          (Real.sin θ) ^ 2 * fourDPrimitive s θ := by
  unfold originalGCIDenominator
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
  dsimp only
  rw [← fourD_reconstruction s hs θ hθIcc]
  norm_num
  ring

theorem fourD_numerator_formula
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain 4 s) :
    originalGCINumerator 4 r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.cos θ *
          (Real.exp (r * Real.cos θ) *
            (Real.sin θ) ^ 2 * fourDPrimitive s θ) := by
  unfold originalGCINumerator
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
  dsimp only
  rw [← fourD_reconstruction s hs θ hθIcc]
  norm_num
  ring

/-- In ambient dimension four, testing the original weak equation with
`sin θ` and integrating the original weighted AC representative gives
the exact forcing moment, including the angular potential contribution. -/
theorem weak_solution_moment_identity_fourD
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 4 r s) :
    originalForcingNorm 4 r =
      3 * originalGCIDenominator 4 r s +
        r * originalGCINumerator 4 r s := by
  have htest : AngularEnergyDomain 4 (sineTestState 4) :=
    sineTestState_mem_energy 4 (by omega)
  have hweak := (hs.2 (sineTestState 4) htest).2.2
  rw [sourcePairing_sine_eq_forcingNorm] at hweak
  have hIBP := fourD_integral_ibp s hs.1 r
  have hu := fourDPrimitive_continuousOn s hs.1
  have hBcont : ContinuousOn (fourDIBPWeight r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    unfold fourDIBPWeight
    fun_prop
  have hRcont : ContinuousOn (fourDRemainderWeight r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    unfold fourDRemainderWeight
    fun_prop
  have hB : IntervalIntegrable
      (fun θ : ℝ => fourDIBPWeight r θ * fourDPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (hBcont.mul hu).intervalIntegrable_of_Icc Real.pi_pos.le
  have hR : IntervalIntegrable
      (fun θ : ℝ => fourDRemainderWeight r θ * fourDPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (hRcont.mul hu).intervalIntegrable_of_Icc Real.pi_pos.le
  have hD : IntervalIntegrable
      (fun θ : ℝ =>
        Real.exp (r * Real.cos θ) *
          (Real.sin θ) ^ 2 * fourDPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
    exact (((by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        (Real.sin θ) ^ 2)).continuousOn).mul hu).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hN : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ *
        (Real.exp (r * Real.cos θ) *
          (Real.sin θ) ^ 2 * fourDPrimitive s θ))
      volume (0 : ℝ) Real.pi := by
    exact (hD.continuousOn_mul Real.continuous_cos.continuousOn).congr
      (by intro θ _; ring)
  calc
    originalForcingNorm 4 r =
        originalWeakForm 4 r s (sineTestState 4) := hweak.symm
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          fourDFluxWeight r θ * s.scaledDerivative θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          fourDRemainderWeight r θ * fourDPrimitive s θ) :=
      fourD_weakForm_sine r s hs
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          fourDIBPWeight r θ * fourDPrimitive s θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          fourDRemainderWeight r θ * fourDPrimitive s θ) := by
      rw [hIBP]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) *
            (Real.sin θ) ^ 2 *
              (3 + r * Real.cos θ) * fourDPrimitive s θ := by
      rw [← intervalIntegral.integral_add hB hR]
      apply intervalIntegral.integral_congr
      intro θ _
      exact fourD_moment_density r θ (fourDPrimitive s θ)
    _ = 3 * originalGCIDenominator 4 r s +
        r * originalGCINumerator 4 r s := by
      rw [fourD_denominator_formula r s hs.1,
        fourD_numerator_formula r s hs.1]
      calc
        _ = ∫ θ in (0 : ℝ)..Real.pi,
              3 * (Real.exp (r * Real.cos θ) *
                (Real.sin θ) ^ 2 * fourDPrimitive s θ) +
              r * (Real.cos θ *
                (Real.exp (r * Real.cos θ) *
                  (Real.sin θ) ^ 2 * fourDPrimitive s θ)) := by
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add (hD.const_mul 3)
            (hN.const_mul r),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]

end

end DFL.GCI
