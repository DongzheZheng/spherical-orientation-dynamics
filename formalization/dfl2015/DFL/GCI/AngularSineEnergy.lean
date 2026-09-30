import DFL.GCI.AngularEnergyCauchy

/-!
# Smooth forcing-test energy identity in every ambient dimension

The flux `sin^(n-1)(θ) exp(r cosθ) cosθ` relates the original sine-test
self-energy to the original forcing norm and a dimension-shifted cosine
moment.  The flux vanishes at both endpoints for every `n≥2`.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def originalShiftMoment (n : ℕ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    angularWeight n r θ * Real.cos θ * (Real.sin θ) ^ 2

private def sineEnergyFlux (n : ℕ) (r θ : ℝ) : ℝ :=
  (Real.sin θ) ^ (n - 1) *
    Real.exp (r * Real.cos θ) * Real.cos θ

private theorem sineEnergyFlux_hasDerivAt
    (n : ℕ) (hn : 2 ≤ n) (r θ : ℝ) :
    HasDerivAt (sineEnergyFlux n r)
      (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) *
          Real.exp (r * Real.cos θ) * Real.sin θ) θ := by
  have hpow : HasDerivAt (fun x : ℝ => (Real.sin x) ^ (n - 1))
      (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow (n - 1) using 1
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hsub]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  have hprod := (hpow.mul harg.exp).mul (Real.hasDerivAt_cos θ)
  convert hprod using 1
  dsimp [sineEnergyFlux]
  ring

theorem angularWeight_eq_sin_pow
    (n : ℕ) (hn : 2 ≤ n) (r θ : ℝ) :
    angularWeight n r θ =
      (Real.sin θ) ^ (n - 2) * Real.exp (r * Real.cos θ) := by
  unfold angularWeight
  have hcast : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub (by omega : 2 ≤ n) :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - (2 : ℝ)).symm
  rw [hcast]
  exact congrArg (fun x : ℝ => x * Real.exp (r * Real.cos θ))
    (Real.rpow_natCast (Real.sin θ) (n - 2))

private theorem sineEnergyFlux_derivative_eq_density
    (n : ℕ) (hn : 2 ≤ n) (r θ : ℝ) :
    (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) *
          Real.exp (r * Real.cos θ) * Real.sin θ) =
      angularWeight n r θ *
          ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)) -
        ((n : ℝ) - 1) * angularWeight n r θ *
          (Real.sin θ) ^ 2 -
        r * angularWeight n r θ * Real.cos θ *
          (Real.sin θ) ^ 2 := by
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  have hpow : (Real.sin θ) ^ (n - 1) =
      (Real.sin θ) ^ (n - 2) * Real.sin θ := by
    rw [hn1, pow_succ]
  rw [angularWeight_eq_sin_pow n hn r θ, hpow]
  linear_combination
    (((n : ℝ) - 2) * (Real.sin θ) ^ (n - 2) *
      Real.exp (r * Real.cos θ)) *
        (Real.sin_sq_add_cos_sq θ)

private theorem angularWeight_continuous
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    Continuous (angularWeight n r) := by
  have hnr : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have hnr' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  unfold angularWeight
  exact ((Real.continuous_rpow_const hnr).comp Real.continuous_sin).mul
    (Real.continuous_exp.comp
      ((continuous_const.mul Real.continuous_cos)))

private theorem sineEnergyFlux_integral_zero
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) *
          Real.exp (r * Real.cos θ) * Real.sin θ)) = 0 := by
  have hcont : ContinuousOn (sineEnergyFlux n r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    exact (by unfold sineEnergyFlux; fun_prop :
      Continuous (sineEnergyFlux n r)).continuousOn
  have hint : IntervalIntegrable
      (fun θ : ℝ =>
        (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
            Real.exp (r * Real.cos θ) * Real.cos θ -
          (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
            Real.exp (r * Real.cos θ) * Real.cos θ -
          (Real.sin θ) ^ (n - 1) *
            Real.exp (r * Real.cos θ) * Real.sin θ))
      volume (0 : ℝ) Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
          Real.exp (r * Real.cos θ) * Real.cos θ -
        (Real.sin θ) ^ (n - 1) *
          Real.exp (r * Real.cos θ) * Real.sin θ))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    Real.pi_pos.le hcont
    (fun θ _ => sineEnergyFlux_hasDerivAt n hn r θ) hint
  have hn0 : n - 1 ≠ 0 := by omega
  simpa [sineEnergyFlux, Real.sin_zero, Real.sin_pi, hn0] using hFTC

/-- For every ambient dimension, the physical sine test has energy
`(n−1)Z+rC`, with `Z` its forcing norm and `C` the next-dimension
angular cosine moment.  This equality is independent of a weak solution. -/
theorem sineTest_self_energy_eq_forcing_add_shift
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    originalWeakForm n r (sineTestState n) (sineTestState n) =
      ((n : ℝ) - 1) * originalForcingNorm n r +
        r * originalShiftMoment n r := by
  have hw := angularWeight_continuous n hn r
  have hT : IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ *
        ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)))
      volume (0 : ℝ) Real.pi :=
    (hw.mul (by fun_prop : Continuous (fun θ : ℝ =>
      (Real.cos θ) ^ 2 + ((n : ℝ) - 2)))).intervalIntegrable _ _
  have hZ : IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hw.mul (by fun_prop : Continuous (fun θ : ℝ =>
      (Real.sin θ) ^ 2))).intervalIntegrable _ _
  have hC : IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ * Real.cos θ *
        (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((hw.mul Real.continuous_cos).mul
      (by fun_prop : Continuous (fun θ : ℝ =>
        (Real.sin θ) ^ 2))).intervalIntegrable _ _
  have hzero := sineEnergyFlux_integral_zero n hn r
  have hlinear :
      (∫ θ in (0 : ℝ)..Real.pi,
        (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ *
            Real.exp (r * Real.cos θ) * Real.cos θ -
          (Real.sin θ) ^ (n - 1) * r * Real.sin θ *
            Real.exp (r * Real.cos θ) * Real.cos θ -
          (Real.sin θ) ^ (n - 1) *
            Real.exp (r * Real.cos θ) * Real.sin θ)) =
        originalWeakForm n r (sineTestState n) (sineTestState n) -
          ((n : ℝ) - 1) * originalForcingNorm n r -
          r * originalShiftMoment n r := by
    rw [sineTest_self_energy_formula, originalForcingNorm,
      originalShiftMoment]
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
            (angularWeight n r θ *
              ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)) -
              ((n : ℝ) - 1) *
                (angularWeight n r θ * (Real.sin θ) ^ 2)) -
              r * (angularWeight n r θ * Real.cos θ *
                (Real.sin θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [sineEnergyFlux_derivative_eq_density n hn r θ]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
            (hT.sub (hZ.const_mul ((n : ℝ) - 1)))
            (hC.const_mul r),
          intervalIntegral.integral_sub hT
            (hZ.const_mul ((n : ℝ) - 1)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  linarith

end

end DFL.GCI
