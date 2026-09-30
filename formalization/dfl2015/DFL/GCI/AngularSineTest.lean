import DFL.GCI.AngularPolarization

/-!
# The physical forcing as an admissible angular test

The test `v(θ)=sin θ` lies in the original represented energy space for
every ambient dimension `n ≥ 2`.  Its weighted `H¹₀` representative is
`sin^(n/2) θ`; this includes the endpoint-sensitive case `n=2`.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def sineTestQ (n : ℕ) (θ : ℝ) : ℝ :=
  ((n : ℝ) / 2) *
    Real.rpow (Real.sin θ) ((n : ℝ) / 2 - 1) * Real.cos θ

def sineTestState (n : ℕ) : AngularState :=
  ⟨Real.sin, sineTestQ n⟩

private theorem sineTestQ_continuous (n : ℕ) (hn : 2 ≤ n) :
    Continuous (sineTestQ n) := by
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 2 - 1 := by
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  unfold sineTestQ
  have hc : Continuous (fun _ : ℝ => (n : ℝ) / 2) := continuous_const
  have hp : Continuous (fun θ : ℝ =>
      Real.rpow (Real.sin θ) ((n : ℝ) / 2 - 1)) :=
    (Real.continuous_rpow_const hexp).comp Real.continuous_sin
  exact (hc.mul hp).mul Real.continuous_cos

private theorem sineTest_scaled_eq (n : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    scaledFunction n (sineTestState n) θ =
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have ha : (0 : ℝ) ≤ halfPower n := by
    unfold halfPower
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsum : halfPower n + 1 = (n : ℝ) / 2 := by
    unfold halfPower
    ring
  change Real.rpow (Real.sin θ) (halfPower n) * Real.sin θ =
    Real.rpow (Real.sin θ) ((n : ℝ) / 2)
  calc
    _ = Real.rpow (Real.sin θ) (halfPower n) *
          Real.rpow (Real.sin θ) 1 := by simp
    _ = Real.rpow (Real.sin θ) (halfPower n + 1) :=
      (Real.rpow_add_of_nonneg hs ha (by norm_num)).symm
    _ = Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by rw [hsum]

private theorem sineTestQ_hasDerivAt (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.rpow (Real.sin s) ((n : ℝ) / 2))
      (sineTestQ n θ) θ := by
  have hp : (1 : ℝ) ≤ (n : ℝ) / 2 := by
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  simpa only [sineTestQ, mul_assoc, mul_comm, mul_left_comm]
    using (Real.hasDerivAt_sin θ).rpow_const (Or.inr hp)

private theorem sineTestQ_integral (n : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    (∫ s in (0 : ℝ)..θ, sineTestQ n s) =
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hcont : ContinuousOn
      (fun s : ℝ => Real.rpow (Real.sin s) ((n : ℝ) / 2))
      (Set.Icc (0 : ℝ) θ) := by
    exact ((Real.continuous_rpow_const hexp).comp
      Real.continuous_sin).continuousOn
  have hint : IntervalIntegrable (sineTestQ n) volume (0 : ℝ) θ :=
    (sineTestQ_continuous n hn).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hθ.1 hcont (fun s _ => sineTestQ_hasDerivAt n hn s) hint
  have hp : ((n : ℝ) / 2) ≠ 0 := by positivity
  simpa [Real.sin_zero, Real.zero_rpow hp] using hFTC

private theorem sineTestPotential_integrable (n : ℕ) (hn : 2 ≤ n) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (((n : ℝ) - 2) *
          Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
          (sineTestState n).g θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  have ha : (0 : ℝ) ≤ halfPower n := by
    unfold halfPower
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hc : Continuous (fun θ : ℝ =>
      (((n : ℝ) - 2) *
        Real.rpow (Real.sin θ) (halfPower n)) ^ 2) := by
    exact (continuous_const.mul
      ((Real.continuous_rpow_const ha).comp Real.continuous_sin)).pow 2
  have hi : IntervalIntegrable
      (fun θ : ℝ =>
        (((n : ℝ) - 2) *
          Real.rpow (Real.sin θ) (halfPower n)) ^ 2)
      volume (0 : ℝ) Real.pi := hc.intervalIntegrable _ _
  apply hi.congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hθ0 : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
    exact ⟨hθ0.1.le, hθ0.2⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
  by_cases hn2 : n = 2
  · subst n
    simp [sineTestState]
  · have hb : (((n : ℝ) - 4) / 2) + 1 ≠ 0 := by
      have hnr : (2 : ℝ) < (n : ℝ) := by
        exact_mod_cast (by omega : 2 < n)
      linarith
    have hsum : (((n : ℝ) - 4) / 2) + 1 = halfPower n := by
      unfold halfPower
      ring
    have hpow :
        Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
          Real.sin θ = Real.rpow (Real.sin θ) (halfPower n) := by
      calc
        _ = Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
              Real.rpow (Real.sin θ) 1 := by simp
        _ = Real.rpow (Real.sin θ)
              ((((n : ℝ) - 4) / 2) + 1) :=
          (Real.rpow_add' hs hb).symm
        _ = Real.rpow (Real.sin θ) (halfPower n) := by rw [hsum]
    change (((n : ℝ) - 2) * Real.rpow (Real.sin θ) (halfPower n)) ^ 2 =
      (((n : ℝ) - 2) *
        Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
        Real.sin θ) ^ 2
    rw [mul_assoc, hpow]

/-- The forcing profile itself is in the represented original source space. -/
theorem sineTestState_mem_energy (n : ℕ) (hn : 2 ≤ n) :
    AngularEnergyDomain n (sineTestState n) := by
  unfold AngularEnergyDomain
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (sineTestQ_continuous n hn).intervalIntegrable _ _
  · exact ((sineTestQ_continuous n hn).pow 2).intervalIntegrable _ _
  · intro θ hθ
    rw [sineTest_scaled_eq n hn θ hθ]
    exact (sineTestQ_integral n hn θ hθ).symm
  · have hπ : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.pi_pos.le, le_rfl⟩
    change (∫ u in (0 : ℝ)..Real.pi, sineTestQ n u) = 0
    rw [sineTestQ_integral n hn Real.pi hπ, Real.sin_pi]
    have hp : ((n : ℝ) / 2) ≠ 0 := by positivity
    simp [Real.zero_rpow hp]
  · exact sineTestPotential_integrable n hn

/-- The pointwise original angular operator on a smooth profile.  This is
the differential expression in DFL's equation before weak integration. -/
def angularOperatorValue (n : ℕ) (r θ y y' y'' : ℝ) : ℝ :=
  -y'' -
    (((n : ℝ) - 2) * Real.cos θ / Real.sin θ -
      r * Real.sin θ) * y' +
    angularPotential n θ * y

/-- Applying the *original* angular differential expression to the
forcing profile yields the exact moment multiplier needed in the GCI
numerator argument.  The assertion is pointwise in the open interval;
transferring it to the original weak form requires integration by parts
for the represented weighted energy domain. -/
theorem angularOperator_sine
    (n : ℕ) (r θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularOperatorValue n r θ
        (Real.sin θ) (Real.cos θ) (-Real.sin θ) =
      ((n : ℝ) - 1 + r * Real.cos θ) * Real.sin θ := by
  have hs : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo hθ).ne'
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold angularOperatorValue angularPotential
  field_simp
  nlinarith

/-- Squared norm of the forcing profile in the original angular weight. -/
def originalForcingNorm (n : ℕ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    angularWeight n r θ * (Real.sin θ) ^ 2

theorem sourcePairing_sine_eq_forcingNorm (n : ℕ) (r : ℝ) :
    originalSourcePairing n r (sineTestState n) =
      originalForcingNorm n r := by
  unfold originalSourcePairing originalForcingNorm sineTestState
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- The forcing norm is strictly positive whenever an original weak
solution exists.  The solution hypothesis supplies the required
integrability of the source pairing with the admissible sine test. -/
theorem originalForcingNorm_pos_of_weak_solution
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    0 < originalForcingNorm n r := by
  rw [← sourcePairing_sine_eq_forcingNorm]
  have htest := sineTestState_mem_energy n hn
  have hint := (hs.2 (sineTestState n) htest).2.1
  unfold originalSourcePairing
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hint
  · intro θ hθ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
    have hw : 0 < angularWeight n r θ := by
      unfold angularWeight
      exact mul_pos (Real.rpow_pos_of_pos hsin _) (Real.exp_pos _)
    change 0 < angularWeight n r θ * Real.sin θ * Real.sin θ
    exact mul_pos (mul_pos hw hsin) hsin
  · exact Real.pi_pos

end

end DFL.GCI
