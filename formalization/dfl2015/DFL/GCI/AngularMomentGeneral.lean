import DFL.GCI.AngularMoment4D

/-!
# The exact forcing moment in ambient dimensions at least four

This file works directly with the represented original weighted `H¹₀`
angular domain.  The flux contains `sin θ ^ ((n-2)/2)`; its exponent is at
least one in the dimensions covered here, so the flux is `C¹` across both
endpoints.  The integration-by-parts boundary terms vanish because the
original weighted representative has the two prescribed zero traces.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def momentPrimitive (s : AngularState) (θ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..θ, s.scaledDerivative u

def momentFlux (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    Real.rpow (Real.sin θ) (halfPower n) * Real.cos θ

def momentIBPWeight (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    Real.rpow (Real.sin θ) (halfPower n - 1) *
      ((Real.sin θ) ^ 2 - halfPower n * (Real.cos θ) ^ 2 +
        r * (Real.sin θ) ^ 2 * Real.cos θ)

def momentRemainderWeight (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    Real.rpow (Real.sin θ) (halfPower n - 1) *
      (((n : ℝ) - 2) - halfPower n * (Real.cos θ) ^ 2)

def momentDenominatorWeight (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    Real.rpow (Real.sin θ) (halfPower n + 1)

private theorem halfPower_one_le (n : ℕ) (hn : 4 ≤ n) :
    (1 : ℝ) ≤ halfPower n := by
  unfold halfPower
  have h : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem halfPower_sub_one_nonneg (n : ℕ) (hn : 4 ≤ n) :
    (0 : ℝ) ≤ halfPower n - 1 := by
  linarith [halfPower_one_le n hn]

theorem momentPrimitive_AC (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    AbsolutelyContinuousOnInterval (momentPrimitive s) 0 Real.pi := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  exact hs.1.absolutelyContinuousOnInterval_intervalIntegral h0

theorem momentPrimitive_continuousOn (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    ContinuousOn (momentPrimitive s) (Set.Icc (0 : ℝ) Real.pi) := by
  simpa only [Set.uIcc_of_le Real.pi_pos.le] using
    (momentPrimitive_AC n s hs).continuousOn

theorem momentFlux_hasDerivAt (n : ℕ) (r θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) : HasDerivAt (momentFlux n r)
      (-momentIBPWeight n r θ) θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hp := (Real.hasDerivAt_sin θ).rpow_const (p := halfPower n)
    (Or.inl hsin.ne')
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  have hprod := (harg.exp.mul hp).mul (Real.hasDerivAt_cos θ)
  have hpow :
      Real.rpow (Real.sin θ) (halfPower n) =
        Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ := by
    have hp1 : halfPower n - 1 + 1 = halfPower n := by ring
    rw [← hp1]
    simpa using Real.rpow_add_one hsin.ne' (halfPower n - 1)
  change Real.sin θ ^ halfPower n =
    Real.sin θ ^ (halfPower n - 1) * Real.sin θ at hpow
  convert hprod using 1
  dsimp [momentFlux, momentIBPWeight]
  rw [hpow]
  ring

private theorem momentFlux_AC (n : ℕ) (hn : 4 ≤ n) (r : ℝ) :
    AbsolutelyContinuousOnInterval (momentFlux n r) 0 Real.pi := by
  have hC1 : ContDiff ℝ 1 (momentFlux n r) := by
    unfold momentFlux
    have hp : ContDiff ℝ 1
        (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower n)) :=
      Real.contDiff_rpow_const_of_le (by
        simpa using halfPower_one_le n hn) |>.comp
        Real.contDiff_sin
    exact (Real.contDiff_exp.comp
      ((contDiff_const.mul Real.contDiff_cos))).mul hp |>.mul
        Real.contDiff_cos
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKu : LipschitzOnWith K (momentFlux n r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  exact hKu.absolutelyContinuousOnInterval

theorem moment_ae_interior :
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

private theorem moment_integral_ibp (n : ℕ) (hn : 4 ≤ n)
    (s : AngularState) (hs : AngularEnergyDomain n s) (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux n r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        momentIBPWeight n r θ * momentPrimitive s θ := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  have huAC := momentPrimitive_AC n s hs
  have hqae := hs.1.ae_hasDerivAt_integral
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux n r θ * s.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        momentFlux n r θ * deriv (momentPrimitive s) θ := by
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
  have huπ : momentPrimitive s Real.pi = 0 := hs.2.2.2.1
  have hIBP := (momentFlux_AC n hn r).integral_mul_deriv_eq_deriv_mul huAC
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentFlux n r θ * deriv (momentPrimitive s) θ := hleft
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
          deriv (momentFlux n r) θ * momentPrimitive s θ) := by
      simpa [hu0, huπ] using hIBP
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          -(deriv (momentFlux n r) θ * momentPrimitive s θ) := by
      rw [intervalIntegral.integral_neg]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentIBPWeight n r θ * momentPrimitive s θ := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      rw [(momentFlux_hasDerivAt n r θ hθ).deriv]
      ring

theorem moment_reconstruction (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    Real.rpow (Real.sin θ) (halfPower n) * s.g θ =
      momentPrimitive s θ := by
  exact hs.2.2.1 θ hθ

theorem moment_weakForm_sine_density (n : ℕ)
    (r : ℝ) (s : AngularState) (hs : AngularEnergyDomain n s)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularWeight n r θ *
      (angularDerivative n s θ *
          angularDerivative n (sineTestState n) θ +
        angularPotential n θ * s.g θ * (sineTestState n).g θ) =
      momentFlux n r θ * s.scaledDerivative θ +
        momentRemainderWeight n r θ * momentPrimitive s θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hrec : momentPrimitive s θ =
      Real.rpow (Real.sin θ) (halfPower n) * s.g θ :=
    (moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩).symm
  have htwo : halfPower n + halfPower n = (n : ℝ) - 2 := by
    unfold halfPower
    ring
  have hpowtwo :
      Real.rpow (Real.sin θ) ((n : ℝ) - 2) =
        Real.rpow (Real.sin θ) (halfPower n) ^ 2 := by
    rw [← htwo]
    change Real.sin θ ^ (halfPower n + halfPower n) =
      (Real.sin θ ^ halfPower n) ^ 2
    rw [Real.rpow_add hsin]
    ring
  have hpowone :
      Real.rpow (Real.sin θ) (halfPower n) =
        Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ := by
    have ha : halfPower n - 1 + 1 = halfPower n := by ring
    rw [← ha]
    simpa using Real.rpow_add_one hsin.ne' (halfPower n - 1)
  rw [sineTest_angularDerivative_interior n θ hθ, hrec]
  unfold angularWeight angularDerivative angularPotential
    sineTestState momentFlux momentRemainderWeight
  simp only
  rw [hpowtwo, hpowone]
  have hsin_ne : Real.sin θ ≠ 0 := hsin.ne'
  have hpow_ne : Real.rpow (Real.sin θ) (halfPower n - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hsin _)
  field_simp [hsin_ne, hpow_ne]
  ring

private theorem momentRemainderWeight_continuous (n : ℕ) (hn : 4 ≤ n)
    (r : ℝ) : Continuous (momentRemainderWeight n r) := by
  have hp : Continuous
      (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower n - 1)) :=
    (Real.continuous_rpow_const (halfPower_sub_one_nonneg n hn)).comp
      Real.continuous_sin
  unfold momentRemainderWeight
  fun_prop

private theorem momentIBPWeight_continuous (n : ℕ) (hn : 4 ≤ n)
    (r : ℝ) : Continuous (momentIBPWeight n r) := by
  have hp : Continuous
      (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower n - 1)) :=
    (Real.continuous_rpow_const (halfPower_sub_one_nonneg n hn)).comp
      Real.continuous_sin
  unfold momentIBPWeight
  fun_prop

private theorem momentDenominatorWeight_continuous (n : ℕ) (hn : 4 ≤ n)
    (r : ℝ) : Continuous (momentDenominatorWeight n r) := by
  have ha : (0 : ℝ) ≤ halfPower n + 1 := by
    linarith [halfPower_one_le n hn]
  have hp : Continuous
      (fun θ : ℝ => Real.rpow (Real.sin θ) (halfPower n + 1)) :=
    (Real.continuous_rpow_const ha).comp Real.continuous_sin
  unfold momentDenominatorWeight
  fun_prop

private theorem moment_weakForm_sine (n : ℕ) (hn : 4 ≤ n)
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    originalWeakForm n r s (sineTestState n) =
      (∫ θ in (0 : ℝ)..Real.pi,
        momentFlux n r θ * s.scaledDerivative θ) +
      (∫ θ in (0 : ℝ)..Real.pi,
        momentRemainderWeight n r θ * momentPrimitive s θ) := by
  have hFcont : ContinuousOn (momentFlux n r)
      (Set.uIcc (0 : ℝ) Real.pi) :=
    (momentFlux_AC n hn r).continuousOn
  have hFq : IntervalIntegrable
      (fun θ : ℝ => momentFlux n r θ * s.scaledDerivative θ)
      volume (0 : ℝ) Real.pi := by
    simpa only [mul_comm] using hs.1.1.continuousOn_mul hFcont
  have hR : IntervalIntegrable
      (fun θ : ℝ => momentRemainderWeight n r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    ((momentRemainderWeight_continuous n hn r).continuousOn.mul
      (momentPrimitive_continuousOn n s hs.1)).intervalIntegrable_of_Icc
        Real.pi_pos.le
  calc
    originalWeakForm n r s (sineTestState n) =
        ∫ θ in (0 : ℝ)..Real.pi,
          momentFlux n r θ * s.scaledDerivative θ +
            momentRemainderWeight n r θ * momentPrimitive s θ := by
      unfold originalWeakForm
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      exact moment_weakForm_sine_density n r s hs.1 θ hθ
    _ = _ := intervalIntegral.integral_add hFq hR

private theorem momentPowerShift (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.rpow (Real.sin θ) (halfPower n - 1) *
        (Real.sin θ) ^ 2 =
      Real.rpow (Real.sin θ) (halfPower n + 1) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have ha : halfPower n - 1 + 2 = halfPower n + 1 := by ring
  change Real.sin θ ^ (halfPower n - 1) * Real.sin θ ^ 2 =
    Real.sin θ ^ (halfPower n + 1)
  have h := (Real.rpow_add hsin (halfPower n - 1) (2 : ℝ)).symm
  rw [ha] at h
  simpa only [Real.rpow_two] using h

private theorem momentPowerDenominator (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
      Real.rpow (Real.sin θ) (halfPower n + 1) *
        Real.rpow (Real.sin θ) (halfPower n) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have ha : halfPower n + 1 + halfPower n = (n : ℝ) - 1 := by
    unfold halfPower
    ring
  rw [← ha]
  change Real.sin θ ^ (halfPower n + 1 + halfPower n) =
    Real.sin θ ^ (halfPower n + 1) * Real.sin θ ^ halfPower n
  exact Real.rpow_add hsin _ _

theorem moment_moment_density (n : ℕ) (r θ u : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    momentIBPWeight n r θ * u + momentRemainderWeight n r θ * u =
      momentDenominatorWeight n r θ *
        (((n : ℝ) - 1) + r * Real.cos θ) * u := by
  have hpow := momentPowerShift n θ hθ
  change Real.sin θ ^ (halfPower n - 1) * Real.sin θ ^ 2 =
    Real.sin θ ^ (halfPower n + 1) at hpow
  have hhalf : 2 * halfPower n = (n : ℝ) - 2 := by
    unfold halfPower
    ring
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsc : 1 - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by
    nlinarith [htrig]
  have hcore :
      (Real.sin θ) ^ 2 - halfPower n * (Real.cos θ) ^ 2 +
          ((n : ℝ) - 2) - halfPower n * (Real.cos θ) ^ 2 =
        (Real.sin θ) ^ 2 * ((n : ℝ) - 1) := by
    calc
      _ = (Real.sin θ) ^ 2 +
          ((n : ℝ) - 2) * (1 - (Real.cos θ) ^ 2) := by
        rw [← hhalf]
        ring
      _ = (Real.sin θ) ^ 2 +
          ((n : ℝ) - 2) * (Real.sin θ) ^ 2 := by rw [hsc]
      _ = _ := by ring
  dsimp [momentIBPWeight, momentRemainderWeight,
    momentDenominatorWeight]
  rw [← hpow]
  calc
    _ = Real.exp (r * Real.cos θ) *
          Real.sin θ ^ (halfPower n - 1) *
          ((Real.sin θ) ^ 2 - halfPower n * (Real.cos θ) ^ 2 +
            ((n : ℝ) - 2) - halfPower n * (Real.cos θ) ^ 2 +
              r * (Real.sin θ) ^ 2 * Real.cos θ) * u := by ring
    _ = Real.exp (r * Real.cos θ) *
          Real.sin θ ^ (halfPower n - 1) *
          ((Real.sin θ) ^ 2 * ((n : ℝ) - 1) +
            r * (Real.sin θ) ^ 2 * Real.cos θ) * u := by rw [hcore]
    _ = _ := by ring

theorem moment_denominator_formula (n : ℕ) (r : ℝ)
    (s : AngularState) (hs : AngularEnergyDomain n s) :
    originalGCIDenominator n r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        momentDenominatorWeight n r θ * momentPrimitive s θ := by
  unfold originalGCIDenominator
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  have hpow := momentPowerDenominator n θ hθ
  have hrec : momentPrimitive s θ =
      Real.rpow (Real.sin θ) (halfPower n) * s.g θ :=
    (moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩).symm
  rw [hrec]
  dsimp [momentDenominatorWeight]
  change Real.sin θ ^ ((n : ℝ) - 1) =
    Real.sin θ ^ (halfPower n + 1) * Real.sin θ ^ halfPower n at hpow
  rw [hpow]
  ring

theorem moment_numerator_formula (n : ℕ) (r : ℝ)
    (s : AngularState) (hs : AngularEnergyDomain n s) :
    originalGCINumerator n r s =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.cos θ * momentDenominatorWeight n r θ * momentPrimitive s θ := by
  unfold originalGCINumerator
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  have hpow := momentPowerDenominator n θ hθ
  have hrec : momentPrimitive s θ =
      Real.rpow (Real.sin θ) (halfPower n) * s.g θ :=
    (moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩).symm
  rw [hrec]
  dsimp [momentDenominatorWeight]
  change Real.sin θ ^ ((n : ℝ) - 1) =
    Real.sin θ ^ (halfPower n + 1) * Real.sin θ ^ halfPower n at hpow
  rw [hpow]
  ring

/-- Exact source moment of the original GCI weak equation in every
ambient dimension `n ≥ 4`.  The original weighted representative supplies
both endpoint traces used by the integration by parts. -/
theorem weak_solution_moment_identity_ge_four
    (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    originalForcingNorm n r =
      ((n : ℝ) - 1) * originalGCIDenominator n r s +
        r * originalGCINumerator n r s := by
  have htest : AngularEnergyDomain n (sineTestState n) :=
    sineTestState_mem_energy n (by omega)
  have hweak := (hs.2 (sineTestState n) htest).2.2
  rw [sourcePairing_sine_eq_forcingNorm] at hweak
  have hIBP := moment_integral_ibp n hn s hs.1 r
  have hu := momentPrimitive_continuousOn n s hs.1
  have hB : IntervalIntegrable
      (fun θ : ℝ => momentIBPWeight n r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (((momentIBPWeight_continuous n hn r).continuousOn).mul hu).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hR : IntervalIntegrable
      (fun θ : ℝ => momentRemainderWeight n r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (((momentRemainderWeight_continuous n hn r).continuousOn).mul hu).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hD : IntervalIntegrable
      (fun θ : ℝ => momentDenominatorWeight n r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi :=
    (((momentDenominatorWeight_continuous n hn r).continuousOn).mul hu).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hN : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ * momentDenominatorWeight n r θ *
        momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := by
    exact (hD.continuousOn_mul Real.continuous_cos.continuousOn).congr
      (by intro θ _; ring)
  calc
    originalForcingNorm n r =
        originalWeakForm n r s (sineTestState n) := hweak.symm
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          momentFlux n r θ * s.scaledDerivative θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          momentRemainderWeight n r θ * momentPrimitive s θ) :=
      moment_weakForm_sine n hn r s hs
    _ = (∫ θ in (0 : ℝ)..Real.pi,
          momentIBPWeight n r θ * momentPrimitive s θ) +
        (∫ θ in (0 : ℝ)..Real.pi,
          momentRemainderWeight n r θ * momentPrimitive s θ) := by
      rw [hIBP]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          momentDenominatorWeight n r θ *
            (((n : ℝ) - 1) + r * Real.cos θ) * momentPrimitive s θ := by
      rw [← intervalIntegral.integral_add hB hR]
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      exact moment_moment_density n r θ (momentPrimitive s θ) hθ
    _ = ((n : ℝ) - 1) * originalGCIDenominator n r s +
        r * originalGCINumerator n r s := by
      rw [moment_denominator_formula n r s hs.1,
        moment_numerator_formula n r s hs.1]
      calc
        _ = ∫ θ in (0 : ℝ)..Real.pi,
              ((n : ℝ) - 1) *
                (momentDenominatorWeight n r θ * momentPrimitive s θ) +
              r * (Real.cos θ * momentDenominatorWeight n r θ *
                momentPrimitive s θ) := by
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add
            (hD.const_mul ((n : ℝ) - 1)) (hN.const_mul r),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]

end

end DFL.GCI
