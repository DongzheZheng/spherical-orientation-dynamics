import DFL.GCI.OriginalUniquenessAll

/-!
# Strict dimension-shifted original GCI comparison

The original energy Cauchy step is strict: equality would make the
original weak solution a scalar multiple of the forcing `sin θ`.
Testing the original equation with `sin θ` and `sin θ cos θ` excludes
that equality at positive field. No monotonicity or extra solution
regularity is assumed.
-/

namespace DFL.GCI

open MeasureTheory Filter
open scoped Interval Topology

noncomputable section

def cosineSineTestQ (n : ℕ) (θ : ℝ) : ℝ :=
  sineTestQ n θ * Real.cos θ -
    Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.sin θ

def cosineSineTestState (n : ℕ) : AngularState :=
  ⟨fun θ => Real.sin θ * Real.cos θ, cosineSineTestQ n⟩

private theorem sinePower_hasDerivAt
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.rpow (Real.sin x) ((n : ℝ) / 2))
      (sineTestQ n θ) θ := by
  have hp : (1 : ℝ) ≤ (n : ℝ) / 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simpa only [sineTestQ, mul_assoc, mul_comm, mul_left_comm] using
    (Real.hasDerivAt_sin θ).rpow_const (Or.inr hp)

private theorem cosineSineTestQ_hasDerivAt
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.rpow (Real.sin x) ((n : ℝ) / 2) * Real.cos x)
      (cosineSineTestQ n θ) θ := by
  convert (sinePower_hasDerivAt n hn θ).mul (Real.hasDerivAt_cos θ) using 1
  dsimp [cosineSineTestQ]
  ring

private theorem cosineSineTestQ_continuous
    (n : ℕ) (hn : 2 ≤ n) : Continuous (cosineSineTestQ n) := by
  have hp : 0 ≤ (n : ℝ) / 2 - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hP := (Real.continuous_rpow_const hp).comp Real.continuous_sin
  have hP0 := (Real.continuous_rpow_const (show 0 ≤ (n : ℝ) / 2 by positivity)).comp
    Real.continuous_sin
  unfold cosineSineTestQ sineTestQ
  exact (((hP.const_mul ((n : ℝ) / 2)).mul Real.continuous_cos).mul
    Real.continuous_cos).sub (hP0.mul Real.continuous_sin)

private theorem cosineSine_scaled_eq
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    scaledFunction n (cosineSineTestState n) θ =
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.cos θ := by
  have hsin := Real.sin_nonneg_of_mem_Icc hθ
  have hp : 0 ≤ halfPower n := by
    unfold halfPower
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsum : halfPower n + 1 = (n : ℝ) / 2 := by unfold halfPower; ring
  have hpow : Real.rpow (Real.sin θ) (halfPower n) * Real.sin θ =
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by
    calc
      _ = Real.rpow (Real.sin θ) (halfPower n) * Real.rpow (Real.sin θ) 1 := by simp
      _ = Real.rpow (Real.sin θ) (halfPower n + 1) :=
        (Real.rpow_add_of_nonneg hsin hp (by norm_num)).symm
      _ = _ := by rw [hsum]
  unfold scaledFunction cosineSineTestState
  rw [← mul_assoc, hpow]

theorem cosineSineTestState_mem_energy
    (n : ℕ) (hn : 2 ≤ n) : AngularEnergyDomain n (cosineSineTestState n) := by
  have hcont := cosineSineTestQ_continuous n hn
  have hFTC (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      (∫ x in (0 : ℝ)..θ, cosineSineTestQ n x) =
        Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.cos θ := by
    have hfun : ContinuousOn
        (fun x : ℝ => Real.rpow (Real.sin x) ((n : ℝ) / 2) * Real.cos x)
        (Set.Icc (0 : ℝ) θ) :=
      (((Real.continuous_rpow_const (by positivity)).comp Real.continuous_sin).mul
        Real.continuous_cos).continuousOn
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 hfun
      (fun x _ => cosineSineTestQ_hasDerivAt n hn x) (hcont.intervalIntegrable _ _)
    have hp : (n : ℝ) / 2 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : Real.rpow (0 : ℝ) ((n : ℝ) / 2) = 0 := Real.zero_rpow hp
    rw [Real.sin_zero, Real.cos_zero, hz, zero_mul, sub_zero] at he
    exact he
  refine ⟨hcont.intervalIntegrable _ _, (hcont.pow 2).intervalIntegrable _ _, ?_, ?_, ?_⟩
  · intro θ hθ
    rw [cosineSine_scaled_eq n hn θ hθ]
    exact (hFTC θ hθ).symm
  · change (∫ u in (0 : ℝ)..Real.pi, cosineSineTestQ n u) = 0
    rw [hFTC Real.pi ⟨Real.pi_pos.le, le_rfl⟩, Real.sin_pi]
    have hp : (n : ℝ) / 2 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : Real.rpow (0 : ℝ) ((n : ℝ) / 2) = 0 := Real.zero_rpow hp
    rw [hz, zero_mul]
  · have hi := ((sineTestState_mem_energy n hn).2.2.2.2).continuousOn_mul
      (Real.continuous_cos.pow 2).continuousOn
    apply hi.congr
    intro θ _
    dsimp [cosineSineTestState, sineTestState]
    ring

theorem cosineSineTest_angularDerivative_interior
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularDerivative n (cosineSineTestState n) θ =
      (Real.cos θ) ^ 2 - (Real.sin θ) ^ 2 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hsum : halfPower n + 1 = (n : ℝ) / 2 := by unfold halfPower; ring
  have hpow : Real.rpow (Real.sin θ) ((n : ℝ) / 2) =
      Real.rpow (Real.sin θ) (halfPower n) * Real.sin θ := by
    rw [← hsum]
    exact Real.rpow_add_one hsin.ne' _
  have hpne : Real.rpow (Real.sin θ) (halfPower n) ≠ 0 :=
    (Real.rpow_pos_of_pos hsin _).ne'
  change (Real.sin θ) ^ ((n : ℝ) / 2) =
    (Real.sin θ) ^ (halfPower n) * Real.sin θ at hpow
  calc
    _ = angularDerivative n (sineTestState n) θ * Real.cos θ - (Real.sin θ) ^ 2 := by
      dsimp [angularDerivative, cosineSineTestState, cosineSineTestQ, sineTestState]
      rw [hpow]
      field_simp [hpne]
      ring
    _ = _ := by rw [sineTest_angularDerivative_interior n θ hθ]; ring

def originalCosineSquareMoment (n : ℕ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    angularWeight n r θ * (Real.cos θ) ^ 2 * (Real.sin θ) ^ 2

private theorem angularWeight_continuous' (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    Continuous (angularWeight n r) := by
  have hfun : angularWeight n r = fun θ =>
      (Real.sin θ) ^ (n - 2) * Real.exp (r * Real.cos θ) := by
    funext θ
    exact angularWeight_eq_sin_pow n hn r θ
  rw [hfun]
  fun_prop

theorem cosineSine_source_eq_shift (n : ℕ) (r : ℝ) :
    originalSourcePairing n r (cosineSineTestState n) = originalShiftMoment n r := by
  unfold originalSourcePairing originalShiftMoment cosineSineTestState
  apply intervalIntegral.integral_congr
  intro θ _
  ring

private def cosineSineFlux (n : ℕ) (r θ : ℝ) : ℝ :=
  (Real.sin θ) ^ (n - 1) * Real.exp (r * Real.cos θ) * (Real.cos θ) ^ 2

private theorem cosineSineFlux_hasDerivAt
    (n : ℕ) (hn : 2 ≤ n) (r θ : ℝ) :
    HasDerivAt (cosineSineFlux n r)
      (angularWeight n r θ *
        (((n : ℝ) - 1) * (Real.cos θ) ^ 3 -
          r * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 -
          2 * (Real.sin θ) ^ 2 * Real.cos θ)) θ := by
  have hp : HasDerivAt (fun x : ℝ => (Real.sin x) ^ (n - 1))
      (((n : ℝ) - 1) * (Real.sin θ) ^ (n - 2) * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow (n - 1) using 1
    rw [show n - 1 - 1 = n - 2 by omega,
      Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have he : HasDerivAt (fun x : ℝ => Real.exp (r * Real.cos x))
      (-r * Real.sin θ * Real.exp (r * Real.cos θ)) θ := by
    convert ((Real.hasDerivAt_cos θ).const_mul r).exp using 1
    ring
  convert (hp.mul he).mul ((Real.hasDerivAt_cos θ).pow 2) using 1
  dsimp [cosineSineFlux]
  rw [angularWeight_eq_sin_pow n hn r θ,
    show n - 1 = n - 2 + 1 by omega, pow_succ]
  ring

theorem sine_cosine_form_eq_moments
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    originalWeakForm n r (sineTestState n) (cosineSineTestState n) =
      ((n : ℝ) - 1) * originalShiftMoment n r + r * originalCosineSquareMoment n r := by
  let F (θ : ℝ) := angularWeight n r θ *
    (((n : ℝ) - 1) * (Real.cos θ) ^ 3 -
      r * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 -
      2 * (Real.sin θ) ^ 2 * Real.cos θ)
  have hw := angularWeight_continuous' n hn r
  have hF : IntervalIntegrable F volume (0 : ℝ) Real.pi := by
    exact (hw.mul (by fun_prop)).intervalIntegrable _ _
  have hC : IntervalIntegrable
      (fun θ => angularWeight n r θ * Real.cos θ * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi := by exact ((hw.mul Real.continuous_cos).mul
        (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hK : IntervalIntegrable
      (fun θ => angularWeight n r θ * (Real.cos θ) ^ 2 * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi := by exact ((hw.mul (Real.continuous_cos.pow 2)).mul
        (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hFzero : (∫ θ in (0 : ℝ)..Real.pi, F θ) = 0 := by
    have hflux : ContinuousOn (cosineSineFlux n r) (Set.Icc (0 : ℝ) Real.pi) := by
      unfold cosineSineFlux
      fun_prop
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hflux
      (fun θ _ => cosineSineFlux_hasDerivAt n hn r θ) hF
    have hn0 : n - 1 ≠ 0 := by omega
    simpa only [cosineSineFlux, Real.sin_pi, Real.sin_zero, zero_pow hn0, zero_mul,
      sub_self] using he
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        (F θ + ((n : ℝ) - 1) * (angularWeight n r θ * Real.cos θ * (Real.sin θ) ^ 2)) +
          r * (angularWeight n r θ * (Real.cos θ) ^ 2 * (Real.sin θ) ^ 2) := by
      unfold originalWeakForm
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [moment_ae_interior] with θ hθ
      rw [sineTest_angularDerivative_interior n θ hθ,
        cosineSineTest_angularDerivative_interior n θ hθ]
      have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_mem_Ioo hθ).ne'
      dsimp [F, sineTestState, cosineSineTestState, angularPotential]
      field_simp [hsin]
      linear_combination
        -((n : ℝ) - 2) * angularWeight n r θ * Real.cos θ *
          (Real.sin_sq_add_cos_sq θ)
    _ = _ := by
      rw [intervalIntegral.integral_add (hF.add (hC.const_mul ((n : ℝ) - 1))) (hK.const_mul r),
        intervalIntegral.integral_add hF (hC.const_mul ((n : ℝ) - 1)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFzero]
      simp only [zero_add, originalShiftMoment, originalCosineSquareMoment]

/-- At positive field a scalar multiple of the physical forcing cannot
solve the original weak equation. The two admissible physical tests
detect the nonconstant original operator multiplier `n-1+r cos θ`. -/
theorem scalar_sine_not_original_weak_solution
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ¬ OriginalWeakGCISolution n r (stateSMul t (sineTestState n)) := by
  intro hs
  have hZpos := originalForcingNorm_pos_of_weak_solution n hn r _ hs
  have h1 := (hs.2 (sineTestState n) (sineTestState_mem_energy n hn)).2.2
  rw [originalWeakForm_stateSMul_left, sourcePairing_sine_eq_forcingNorm,
    sineTest_self_energy_eq_forcing_add_shift n hn r] at h1
  have h2 := (hs.2 (cosineSineTestState n) (cosineSineTestState_mem_energy n hn)).2.2
  rw [originalWeakForm_stateSMul_left, cosineSine_source_eq_shift,
    sine_cosine_form_eq_moments n hn r] at h2
  have htne : t ≠ 0 := by
    intro ht
    rw [ht, zero_mul] at h1
    linarith
  let a : ℝ := t * ((n : ℝ) - 1) - 1
  let b : ℝ := t * r
  have hbne : b ≠ 0 := mul_ne_zero htne hr.ne'
  have he1 : a * originalForcingNorm n r + b * originalShiftMoment n r = 0 := by
    dsimp [a, b]
    nlinarith [h1]
  have he2 : a * originalShiftMoment n r + b * originalCosineSquareMoment n r = 0 := by
    dsimp [a, b]
    nlinarith [h2]
  have hw := angularWeight_continuous' n hn r
  have hZ : IntervalIntegrable
      (fun θ => angularWeight n r θ * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hw.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hC : IntervalIntegrable
      (fun θ => angularWeight n r θ * Real.cos θ * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((hw.mul Real.continuous_cos).mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hK : IntervalIntegrable
      (fun θ => angularWeight n r θ * (Real.cos θ) ^ 2 * (Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((hw.mul (Real.continuous_cos.pow 2)).mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hquad :
      (∫ θ in (0 : ℝ)..Real.pi,
        angularWeight n r θ * (Real.sin θ) ^ 2 * (a + b * Real.cos θ) ^ 2) =
      a ^ 2 * originalForcingNorm n r +
        (2 * a * b) * originalShiftMoment n r + b ^ 2 * originalCosineSquareMoment n r := by
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
          (a ^ 2 * (angularWeight n r θ * (Real.sin θ) ^ 2) +
            (2 * a * b) * (angularWeight n r θ * Real.cos θ * (Real.sin θ) ^ 2)) +
            b ^ 2 * (angularWeight n r θ * (Real.cos θ) ^ 2 * (Real.sin θ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hZ.const_mul (a ^ 2)).add (hC.const_mul (2 * a * b))) (hK.const_mul (b ^ 2)),
          intervalIntegral.integral_add (hZ.const_mul (a ^ 2)) (hC.const_mul (2 * a * b)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        rfl
  have hquadpos : 0 < ∫ θ in (0 : ℝ)..Real.pi,
      angularWeight n r θ * (Real.sin θ) ^ 2 * (a + b * Real.cos θ) ^ 2 := by
    have hcont : ContinuousOn
        (fun θ => angularWeight n r θ * (Real.sin θ) ^ 2 * (a + b * Real.cos θ) ^ 2)
        (Set.Icc (0 : ℝ) Real.pi) := by exact
      ((hw.mul (Real.continuous_sin.pow 2)).mul (by fun_prop)).continuousOn
    apply intervalIntegral.integral_pos Real.pi_pos hcont
    · intro θ hθ
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, hθ.2⟩
      unfold angularWeight
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hsin _) (Real.exp_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
    · by_cases ha : a = 0
      · refine ⟨Real.pi / 3, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
        have hθ : Real.pi / 3 ∈ Set.Ioo (0 : ℝ) Real.pi :=
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hsin := Real.sin_pos_of_mem_Ioo hθ
        have hcoef : a + b * Real.cos (Real.pi / 3) ≠ 0 := by
          rw [ha, Real.cos_pi_div_three]
          simp only [zero_add]
          exact mul_ne_zero hbne (by norm_num)
        unfold angularWeight
        exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hsin _) (Real.exp_pos _))
          (sq_pos_of_pos hsin)) (sq_pos_of_ne_zero hcoef)
      · refine ⟨Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
        have hsin : 0 < Real.sin (Real.pi / 2) := by rw [Real.sin_pi_div_two]; norm_num
        have hcoef : a + b * Real.cos (Real.pi / 2) ≠ 0 := by
          simpa only [Real.cos_pi_div_two, mul_zero, add_zero] using ha
        unfold angularWeight
        exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hsin _) (Real.exp_pos _))
          (sq_pos_of_pos hsin)) (sq_pos_of_ne_zero hcoef)
  have hem1 := congrArg (fun x : ℝ => a * x) he1
  have hem2 := congrArg (fun x : ℝ => b * x) he2
  rw [hquad] at hquadpos
  nlinarith [hem1, hem2]

private theorem originalWeakForm_symmetric
    (n : ℕ) (r : ℝ) (s v : AngularState) :
    originalWeakForm n r s v = originalWeakForm n r v s := by
  unfold originalWeakForm
  apply intervalIntegral.integral_congr
  intro θ _
  ring

private theorem form_scalar_sub_expansion
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s v : AngularState) (t : ℝ)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v) :
    originalWeakForm n r (stateSub s (stateSMul t v)) (stateSub s (stateSMul t v)) =
      originalWeakForm n r s s - 2 * t * originalWeakForm n r s v +
        t ^ 2 * originalWeakForm n r v v := by
  have hsz := stateSub_mem_energy n hn s (stateSMul t v) hs (stateSMul_mem_energy n v hv t)
  have htv := stateSMul_mem_energy n v hv t
  have hntv := stateSMul_mem_energy n (stateSMul t v) htv (-1)
  unfold stateSub
  rw [originalWeakForm_stateAdd_left n hn r s (stateSMul (-1) (stateSMul t v))
    (stateAdd s (stateSMul (-1) (stateSMul t v))) hs hntv hsz,
    originalWeakForm_stateSMul_left, originalWeakForm_stateSMul_left]
  rw [originalWeakForm_symmetric n r s (stateAdd s (stateSMul (-1) (stateSMul t v))),
    originalWeakForm_stateAdd_left n hn r s (stateSMul (-1) (stateSMul t v)) s hs hntv hs,
    originalWeakForm_stateSMul_left, originalWeakForm_stateSMul_left,
    originalWeakForm_symmetric n r v (stateAdd s (stateSMul (-1) (stateSMul t v))),
    originalWeakForm_stateAdd_left n hn r s (stateSMul (-1) (stateSMul t v)) v hs hntv hv,
    originalWeakForm_stateSMul_left, originalWeakForm_stateSMul_left,
    originalWeakForm_symmetric n r v s]
  ring

/-- Original energy Cauchy is strict for every original represented
source weak solution in every ambient dimension at least three. -/
theorem weak_solution_forcing_energy_cauchy_strict_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    (originalForcingNorm n r) ^ 2 <
      originalGCIDenominator n r s *
        originalWeakForm n r (sineTestState n) (sineTestState n) := by
  let Z := originalForcingNorm n r
  let D := originalGCIDenominator n r s
  let T := originalWeakForm n r (sineTestState n) (sineTestState n)
  have hZpos : 0 < Z := originalForcingNorm_pos_of_weak_solution n (by omega) r s hs
  have hDpos : 0 < D := weak_solution_denominator_pos n (by omega) r s hs
  have hC : Z ^ 2 ≤ D * T := weak_solution_forcing_energy_cauchy n (by omega) r s hs
  have hTpos : 0 < T := by
    by_contra h
    have hTle : T ≤ 0 := le_of_not_gt h
    have hprod := mul_nonpos_of_nonneg_of_nonpos hDpos.le hTle
    nlinarith [sq_pos_of_pos hZpos]
  by_contra hnot
  have hEq : Z ^ 2 = D * T := le_antisymm hC (le_of_not_gt hnot)
  let t := Z / T
  have ht : t * T = Z := div_mul_cancel₀ _ hTpos.ne'
  let e := stateSMul t (sineTestState n)
  let z := stateSub s e
  have hsin := sineTestState_mem_energy n (by omega)
  have hedom : AngularEnergyDomain n e := stateSMul_mem_energy n _ hsin t
  have hzdom : AngularEnergyDomain n z := stateSub_mem_energy n (by omega) s e hs.1 hedom
  have hself : originalWeakForm n r s s = D :=
    (hs.2 s hs.1).2.2.trans (originalSourcePairing_eq_denominator n (by omega) r s)
  have hcross : originalWeakForm n r s (sineTestState n) = Z :=
    (hs.2 (sineTestState n) hsin).2.2.trans (sourcePairing_sine_eq_forcingNorm n r)
  have hE : originalWeakForm n r z z = D - 2 * t * Z + t ^ 2 * T := by
    rw [form_scalar_sub_expansion n (by omega) r s (sineTestState n) t hs.1 hsin,
      hself, hcross]
  have hEz : originalWeakForm n r z z = 0 := by
    have hmul : originalWeakForm n r z z * T = 0 := by
      rw [hE]
      calc
        (D - 2 * t * Z + t ^ 2 * T) * T = D * T - (t * T) ^ 2 := by rw [← ht]; ring
        _ = 0 := by rw [ht, ← hEq]; ring
    exact (mul_eq_zero.mp hmul).resolve_right hTpos.ne'
  have hzero := energyDomain_self_energy_zero_primitive_ge_three n hn r z hzdom hEz
  have hg : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, e.g θ = s.g θ := by
    intro θ hθ
    have hrec := moment_reconstruction n z hzdom θ ⟨hθ.1.le, hθ.2.le⟩
    rw [hzero θ hθ] at hrec
    have hp : Real.rpow (Real.sin θ) (halfPower n) ≠ 0 :=
      (Real.rpow_pos_of_pos (Real.sin_pos_of_mem_Ioo hθ) _).ne'
    have hmul : Real.rpow (Real.sin θ) (halfPower n) * (s.g θ - e.g θ) = 0 := by
      simpa only [z, scaledFunction, stateSub, stateAdd, stateSMul, neg_one_mul,
        ← sub_eq_add_neg] using hrec
    have heq := (mul_eq_zero.mp hmul).resolve_left hp
    linarith
  have hq : e.scaledDerivative =ᵐ[angularIntervalMeasure] s.scaledDerivative := by
    filter_upwards [moment_ae_interior, momentPrimitive_deriv_ae n z hzdom] with θ hθ hdu
    have hlocal : momentPrimitive z =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
      exact hzero x hx
    have hder : deriv (momentPrimitive z) θ = 0 :=
      ((hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv
    rw [hdu] at hder
    dsimp [z, stateSub, stateAdd, stateSMul] at hder
    change e.scaledDerivative θ = s.scaledDerivative θ
    dsimp [e, stateSMul] at hder ⊢
    linarith
  have heWeak : OriginalWeakGCISolution n r e := by
    refine ⟨hedom, ?_⟩
    intro v hv
    refine ⟨formIntegrand_intervalIntegrable_of_energyDomain n (by omega) r e v hedom hv,
      source_intervalIntegrable_of_energyDomain n (by omega) r v hv, ?_⟩
    calc
      originalWeakForm n r e v = originalWeakForm n r s v := by
        unfold originalWeakForm
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [hq, moment_ae_interior] with θ hqθ hθ
        unfold angularDerivative
        rw [hg θ hθ, hqθ]
      _ = originalSourcePairing n r v := (hs.2 v hv).2.2
  exact scalar_sine_not_original_weak_solution n (by omega) r hr t heWeak

/-- Strict comparison with the true orientation mean two ambient
dimensions higher, proved from the original weak equation and domain. -/
theorem weak_solution_coefficient_lt_shift_mean_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    originalGCICoefficient n r s < DFL.orientationMean (n + 2) r := by
  have hD := weak_solution_denominator_pos n (by omega) r s hs
  have hZ := originalForcingNorm_pos_of_weak_solution n (by omega) r s hs
  have hC := weak_solution_forcing_energy_cauchy_strict_ge_three n hn r hr s hs
  have hT := sineTest_self_energy_eq_forcing_add_shift n (by omega) r
  rw [hT] at hC
  have hM := weak_solution_moment_identity_all n (by omega) r s hs
  have hND : originalForcingNorm n r * originalGCINumerator n r s <
      originalGCIDenominator n r s * originalShiftMoment n r := by
    have hbound : r * (originalForcingNorm n r * originalGCINumerator n r s) <
        r * (originalGCIDenominator n r s * originalShiftMoment n r) := by
      nlinarith [hC, congrArg (fun x : ℝ => originalForcingNorm n r * x) hM]
    exact (mul_lt_mul_iff_right₀ hr).mp hbound
  rw [orientationMean_shift_eq_angular_shift_ratio n (by omega) r]
  unfold originalGCICoefficient
  exact (div_lt_div_iff₀ hD hZ).2 (by nlinarith [hND])

theorem original_GCI_strict_shift_chain_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s < DFL.orientationMean (n + 2) r ∧
      DFL.orientationMean (n + 2) r < DFL.orientationMean n r :=
  ⟨original_GCI_positive_ge_three n hn r hr s hs,
    weak_solution_coefficient_lt_shift_mean_ge_three n hn r hr s hs,
    DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift n (by omega) hr⟩


end

end DFL.GCI
