import DFL.GCI.EnergyDomainLinear

/-!
# The original forcing–mass inequality in all dimensions

All terms use the same original Dirichlet representative. The strict
spectral premise at the end is stated explicitly and discharged separately.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def originalWeightedMass (r : ℝ) (s : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (r * Real.cos θ) * (momentPrimitive s θ) ^ 2

def forcingAmplitude (n : ℕ) (θ : ℝ) : ℝ :=
  Real.rpow (Real.sin θ) ((n : ℝ) / 2)

theorem forcingAmplitude_continuous (n : ℕ) :
    Continuous (forcingAmplitude n) := by
  unfold forcingAmplitude
  exact (Real.continuous_rpow_const (by positivity)).comp Real.continuous_sin

theorem originalWeightedMass_integrable (n : ℕ) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => Real.exp (r * Real.cos θ) *
      (momentPrimitive s θ) ^ 2) volume (0 : ℝ) Real.pi :=
  ((by fun_prop : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ))).continuousOn.mul
    ((momentPrimitive_continuousOn n s hs).pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le

theorem original_denominator_mass_formula (n : ℕ) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    originalGCIDenominator n r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * forcingAmplitude n θ * momentPrimitive s θ := by
  unfold originalGCIDenominator
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  rw [denominator_density_eq_scaled n s hs r θ hθ]
  unfold momentDenominatorWeight forcingAmplitude
  have hp : halfPower n + 1 = (n : ℝ) / 2 := by unfold halfPower; ring
  rw [hp]

theorem original_forcingNorm_mass_formula (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    originalForcingNorm n r =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * (forcingAmplitude n θ) ^ 2 := by
  unfold originalForcingNorm
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hsq : (forcingAmplitude n θ) ^ 2 = (Real.sin θ) ^ n := by
    unfold forcingAmplitude
    have hp : (n : ℝ) / 2 + (n : ℝ) / 2 = n := by ring
    calc
      _ = (Real.sin θ) ^ ((n : ℝ) / 2) * (Real.sin θ) ^ ((n : ℝ) / 2) := by
        change ((Real.sin θ) ^ ((n : ℝ) / 2)) ^ 2 = _
        ring
      _ = (Real.sin θ) ^ ((n : ℝ) / 2 + (n : ℝ) / 2) :=
        (Real.rpow_add hsin _ _).symm
      _ = (Real.sin θ) ^ n := by rw [hp]; exact Real.rpow_natCast _ _
  rw [angularWeight_eq_sin_pow n hn r θ, hsq]
  have hn2 : n = n - 2 + 2 := by omega
  nth_rw 2 [hn2]
  rw [pow_add]
  ring

theorem weak_solution_weighted_mass_cauchy_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    (originalGCIDenominator n r s) ^ 2 ≤
      originalForcingNorm n r * originalWeightedMass r s := by
  have hZpos := originalForcingNorm_pos_of_weak_solution n hn r s hs
  have hM := originalWeightedMass_integrable n r s hs.1
  have hu := momentPrimitive_continuousOn n s hs.1
  have hw : ContinuousOn (fun θ : ℝ => Real.exp (r * Real.cos θ))
      (Set.Icc (0 : ℝ) Real.pi) := (by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ))).continuousOn
  have hβ : ContinuousOn (forcingAmplitude n) (Set.Icc (0 : ℝ) Real.pi) :=
    (forcingAmplitude_continuous n).continuousOn
  have hD : IntervalIntegrable (fun θ => Real.exp (r * Real.cos θ) *
      forcingAmplitude n θ * momentPrimitive s θ) volume (0 : ℝ) Real.pi :=
    ((hw.mul hβ).mul hu).intervalIntegrable_of_Icc Real.pi_pos.le
  have hZ : IntervalIntegrable (fun θ => Real.exp (r * Real.cos θ) *
      (forcingAmplitude n θ) ^ 2) volume (0 : ℝ) Real.pi :=
    (hw.mul (hβ.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
  let t := originalGCIDenominator n r s / originalForcingNorm n r
  have ht : t * originalForcingNorm n r = originalGCIDenominator n r s :=
    div_mul_cancel₀ _ hZpos.ne'
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos θ) *
        (momentPrimitive s θ - t * forcingAmplitude n θ) ^ 2 := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    positivity
  have hquad : (∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos θ) *
        (momentPrimitive s θ - t * forcingAmplitude n θ) ^ 2) =
      originalWeightedMass r s - (2 * t) * originalGCIDenominator n r s +
        t ^ 2 * originalForcingNorm n r := by
    rw [originalWeightedMass, original_denominator_mass_formula n r s hs.1,
      original_forcingNorm_mass_formula n hn r]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
          (Real.exp (r * Real.cos θ) * (momentPrimitive s θ) ^ 2 -
            (2 * t) * (Real.exp (r * Real.cos θ) * forcingAmplitude n θ * momentPrimitive s θ)) +
            t ^ 2 * (Real.exp (r * Real.cos θ) * (forcingAmplitude n θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hM.sub (hD.const_mul (2 * t))) (hZ.const_mul (t ^ 2)),
          intervalIntegral.integral_sub hM (hD.const_mul (2 * t)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hquad] at hnonneg
  have ht2 : t ^ 2 * originalForcingNorm n r = t * originalGCIDenominator n r s := by
    calc
      _ = t * (t * originalForcingNorm n r) := by ring
      _ = _ := by rw [ht]
  have hMD : t * originalGCIDenominator n r s ≤ originalWeightedMass r s := by linarith
  have hmul := mul_le_mul_of_nonneg_right hMD hZpos.le
  have hprod : t * originalGCIDenominator n r s * originalForcingNorm n r =
      (originalGCIDenominator n r s) ^ 2 := by
    calc
      _ = (t * originalForcingNorm n r) * originalGCIDenominator n r s := by ring
      _ = _ := by rw [ht]; ring
  nlinarith

theorem weak_solution_primitive_nonzero_interior
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) Real.pi, momentPrimitive s θ ≠ 0 := by
  by_contra hnone
  have hz : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, momentPrimitive s θ = 0 := by
    simpa only [not_exists, not_and, not_not] using hnone
  have hDzero : originalGCIDenominator n r s = 0 := by
    rw [original_denominator_mass_formula n r s hs.1]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [moment_ae_interior] with θ hθ
        rw [hz θ hθ]
        ring
      _ = 0 := by simp
  have hDpos := weak_solution_denominator_pos n hn r s hs
  linarith

theorem weak_solution_numerator_pos_of_strict_spectral_gap
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hgap : ((n : ℝ) - 1) * originalWeightedMass r s < originalWeakForm n r s s) :
    0 < originalGCINumerator n r s := by
  have hDpos := weak_solution_denominator_pos n hn r s hs
  have hZpos := originalForcingNorm_pos_of_weak_solution n hn r s hs
  have hEnergy : originalWeakForm n r s s = originalGCIDenominator n r s :=
    (hs.2 s hs.1).2.2.trans (originalSourcePairing_eq_denominator n hn r s)
  have hgap' : ((n : ℝ) - 1) * originalWeightedMass r s < originalGCIDenominator n r s := by
    rwa [hEnergy] at hgap
  have hCauchy := weak_solution_weighted_mass_cauchy_all n hn r s hs
  have hng : 0 ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hZgreater : ((n : ℝ) - 1) * originalGCIDenominator n r s < originalForcingNorm n r := by
    by_contra h
    have hle := le_of_not_gt h
    have hprod := mul_le_mul_of_nonneg_right hle hDpos.le
    have hspec := mul_lt_mul_of_pos_left hgap' hZpos
    have hmc := mul_le_mul_of_nonneg_left hCauchy hng
    nlinarith
  have hMoment := weak_solution_moment_identity_all n hn r s hs
  have hRN : 0 < r * originalGCINumerator n r s := by linarith
  exact (mul_pos_iff_of_pos_left hr).mp hRN

end

end DFL.GCI
