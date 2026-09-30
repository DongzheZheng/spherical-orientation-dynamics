import DFL.GCI.AngularEnergy

/-!
# A concrete nonzero test in the original angular energy domain

The weighted `H¹₀` variable is chosen as `u(θ)=sin^n θ`; its derivative is
an elementary polynomial in `sin θ` and `cos θ`.  This constructs an
actual admissible positive test for the source functional in every ambient
dimension `n≥2`.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def positiveTestG (n : ℕ) (θ : ℝ) : ℝ :=
  Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2)

def positiveTestQ (n : ℕ) (θ : ℝ) : ℝ :=
  (n : ℝ) * (Real.sin θ) ^ (n - 1) * Real.cos θ

def positiveTestState (n : ℕ) : AngularState :=
  ⟨positiveTestG n, positiveTestQ n⟩

private theorem positiveTestQ_continuous (n : ℕ) :
    Continuous (positiveTestQ n) := by
  unfold positiveTestQ
  fun_prop

private theorem test_scaled_eq (n : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    scaledFunction n (positiveTestState n) θ = (Real.sin θ) ^ n := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have ha : (0 : ℝ) ≤ halfPower n := by
    unfold halfPower
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hb : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  have hsum : halfPower n + ((n : ℝ) + 2) / 2 = (n : ℝ) := by
    unfold halfPower
    ring
  change Real.rpow (Real.sin θ) (halfPower n) *
      Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2) =
    (Real.sin θ) ^ n
  calc
    _ = Real.rpow (Real.sin θ)
        (halfPower n + ((n : ℝ) + 2) / 2) :=
      (Real.rpow_add_of_nonneg hs ha hb).symm
    _ = Real.rpow (Real.sin θ) (n : ℝ) := by rw [hsum]
    _ = (Real.sin θ) ^ n := Real.rpow_natCast _ _

private theorem positiveTestQ_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.sin s) ^ n)
      (positiveTestQ n θ) θ := by
  unfold positiveTestQ
  convert (Real.hasDerivAt_sin θ).pow n using 1

private theorem positiveTestQ_integral (n : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    (∫ s in (0 : ℝ)..θ, positiveTestQ n s) = (Real.sin θ) ^ n := by
  have hcont : ContinuousOn (fun s : ℝ => (Real.sin s) ^ n)
      (Set.Icc (0 : ℝ) θ) := by fun_prop
  have hint : IntervalIntegrable (positiveTestQ n) volume (0 : ℝ) θ :=
    (positiveTestQ_continuous n).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hθ.1 hcont (fun s _ => positiveTestQ_hasDerivAt n s) hint
  have hn0 : n ≠ 0 := by omega
  simpa [Real.sin_zero, hn0] using hFTC

private theorem positiveTestPotential_integrable (n : ℕ) (hn : 2 ≤ n) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (((n : ℝ) - 2) *
          Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
          positiveTestG n θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  have hc : Continuous (fun θ : ℝ =>
      (((n : ℝ) - 2) * (Real.sin θ) ^ (n - 1)) ^ 2) := by fun_prop
  have hi : IntervalIntegrable
      (fun θ : ℝ => (((n : ℝ) - 2) * (Real.sin θ) ^ (n - 1)) ^ 2)
      volume (0 : ℝ) Real.pi := hc.intervalIntegrable _ _
  apply hi.congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hθ0 : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
    exact ⟨hθ0.1.le, hθ0.2⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
  have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hexp : (((n : ℝ) - 4) / 2) + (((n : ℝ) + 2) / 2) =
      ((n : ℝ) - 1) := by ring
  have hne : (((n : ℝ) - 4) / 2) + (((n : ℝ) + 2) / 2) ≠ 0 := by
    rw [hexp]
    linarith
  have hnat : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hpow :
      Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
        Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2) =
      (Real.sin θ) ^ (n - 1) := by
    calc
      _ = Real.rpow (Real.sin θ)
            ((((n : ℝ) - 4) / 2) + (((n : ℝ) + 2) / 2)) :=
        (Real.rpow_add' hs hne).symm
      _ = Real.rpow (Real.sin θ) ((n : ℝ) - 1) := by rw [hexp]
      _ = (Real.sin θ) ^ (n - 1) := by
        rw [hnat]
        exact Real.rpow_natCast _ _
  change (((n : ℝ) - 2) * (Real.sin θ) ^ (n - 1)) ^ 2 =
    (((n : ℝ) - 2) *
      Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
      positiveTestG n θ) ^ 2
  unfold positiveTestG
  rw [mul_assoc, hpow]

/-- The concrete test is in the *represented original `V`*, for every
ambient dimension `n ≥ 2`, including the endpoint-sensitive circle. -/
theorem positiveTestState_mem_energy (n : ℕ) (hn : 2 ≤ n) :
    AngularEnergyDomain n (positiveTestState n) := by
  unfold AngularEnergyDomain
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (positiveTestQ_continuous n).intervalIntegrable _ _
  · have hc : Continuous (fun θ : ℝ => (positiveTestQ n θ) ^ 2) := by
      exact (positiveTestQ_continuous n).pow 2
    exact hc.intervalIntegrable _ _
  · intro θ hθ
    rw [test_scaled_eq n hn θ hθ]
    exact (positiveTestQ_integral n hn θ hθ).symm
  · have hπ : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.pi_pos.le, le_rfl⟩
    change (∫ u in (0 : ℝ)..Real.pi, positiveTestQ n u) = 0
    rw [positiveTestQ_integral n hn Real.pi hπ, Real.sin_pi]
    have hn0 : n ≠ 0 := by omega
    simp [hn0]
  · change IntervalIntegrable
      (fun θ : ℝ =>
        (((n : ℝ) - 2) *
          Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) *
          positiveTestG n θ) ^ 2)
      volume (0 : ℝ) Real.pi
    exact positiveTestPotential_integrable n hn

/-- Every original weak solution must pair with this concrete admissible
test to give a *strictly positive* source value.  This is the nonzero
forcing needed for a later coercivity/polarization argument. -/
theorem positiveTest_source_pos_of_weak_solution
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    0 < originalSourcePairing n r (positiveTestState n) := by
  have htest := positiveTestState_mem_energy n hn
  have hsrcint := (hs.2 (positiveTestState n) htest).2.1
  unfold originalSourcePairing
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hsrcint
  · intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_mem_Ioo hθ
    have hw : 0 < angularWeight n r θ := by
      unfold angularWeight
      exact mul_pos (Real.rpow_pos_of_pos hsin _)
        (Real.exp_pos _)
    have hg : 0 < (positiveTestState n).g θ := by
      change 0 < positiveTestG n θ
      unfold positiveTestG
      exact Real.rpow_pos_of_pos hsin _
    exact mul_pos (mul_pos hw hsin) hg
  · exact Real.pi_pos

private theorem positiveTest_angularDerivative_interior
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularDerivative n (positiveTestState n) θ =
      (((n : ℝ) + 2) / 2) *
        Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.cos θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hnat : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hprod :
      Real.rpow (Real.sin θ) (halfPower n - 1) *
        Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2) =
      (Real.sin θ) ^ (n - 1) := by
    calc
      _ = Real.rpow (Real.sin θ)
          ((halfPower n - 1) + (((n : ℝ) + 2) / 2)) :=
        (Real.rpow_add hs _ _).symm
      _ = Real.rpow (Real.sin θ) ((n : ℝ) - 1) := by
        congr 1
        unfold halfPower
        ring
      _ = Real.rpow (Real.sin θ) ((n - 1 : ℕ) : ℝ) := by rw [hnat]
      _ = (Real.sin θ) ^ (n - 1) := Real.rpow_natCast _ _
  have hquot :
      (Real.sin θ) ^ (n - 1) /
        Real.rpow (Real.sin θ) (halfPower n) =
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by
    calc
      _ = Real.rpow (Real.sin θ) ((n : ℝ) - 1) /
            Real.rpow (Real.sin θ) (halfPower n) := by
        rw [hnat]
        exact congrArg (fun x : ℝ => x / Real.rpow (Real.sin θ) (halfPower n))
          (Real.rpow_natCast (Real.sin θ) (n - 1)).symm
      _ = Real.rpow (Real.sin θ)
            (((n : ℝ) - 1) - halfPower n) :=
        (Real.rpow_sub hs _ _).symm
      _ = Real.rpow (Real.sin θ) ((n : ℝ) / 2) := by
        congr 1
        unfold halfPower
        ring
  have hcoeff : (n : ℝ) - halfPower n = ((n : ℝ) + 2) / 2 := by
    unfold halfPower
    ring
  change
    (((n : ℝ) * (Real.sin θ) ^ (n - 1) * Real.cos θ -
      halfPower n * Real.cos θ *
        Real.rpow (Real.sin θ) (halfPower n - 1) *
        Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2)) /
      Real.rpow (Real.sin θ) (halfPower n)) = _
  calc
    _ = ((n : ℝ) * (Real.sin θ) ^ (n - 1) * Real.cos θ -
          halfPower n * Real.cos θ *
            (Real.rpow (Real.sin θ) (halfPower n - 1) *
              Real.rpow (Real.sin θ) (((n : ℝ) + 2) / 2))) /
          Real.rpow (Real.sin θ) (halfPower n) := by ring
    _ = (((n : ℝ) - halfPower n) *
          (Real.sin θ) ^ (n - 1) * Real.cos θ) /
          Real.rpow (Real.sin θ) (halfPower n) := by
      rw [hprod]
      ring
    _ = ((n : ℝ) - halfPower n) *
          ((Real.sin θ) ^ (n - 1) /
            Real.rpow (Real.sin θ) (halfPower n)) * Real.cos θ := by ring
    _ = (((n : ℝ) + 2) / 2) *
          Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.cos θ := by
      rw [hcoeff, hquot]

private theorem positiveTest_angularDerivative_pi
    (n : ℕ) (hn : 2 ≤ n) :
    angularDerivative n (positiveTestState n) Real.pi = 0 := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hb : (((n : ℝ) + 2) / 2) ≠ 0 := by positivity
  have hq : positiveTestQ n Real.pi = 0 := by
    simp [positiveTestQ, Real.sin_pi, hn1]
  have hg : positiveTestG n Real.pi = 0 := by
    simp [positiveTestG, Real.sin_pi, Real.zero_rpow hb]
  change (positiveTestQ n Real.pi -
      halfPower n * Real.cos Real.pi *
        Real.rpow (Real.sin Real.pi) (halfPower n - 1) *
        positiveTestG n Real.pi) /
      Real.rpow (Real.sin Real.pi) (halfPower n) = 0
  rw [hq, hg]
  simp

private theorem positiveTest_angularDerivative_Ioc
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) Real.pi) :
    angularDerivative n (positiveTestState n) θ =
      (((n : ℝ) + 2) / 2) *
        Real.rpow (Real.sin θ) ((n : ℝ) / 2) * Real.cos θ := by
  by_cases hπ : θ = Real.pi
  · subst θ
    rw [positiveTest_angularDerivative_pi n hn, Real.sin_pi]
    have hnp : ((n : ℝ) / 2) ≠ 0 := by positivity
    simp [Real.zero_rpow hnp]
  · exact positiveTest_angularDerivative_interior n hn θ
      ⟨hθ.1, lt_of_le_of_ne hθ.2 hπ⟩

private theorem positiveTest_potential_interior
    (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularPotential n θ * (positiveTestState n).g θ *
      (positiveTestState n).g θ =
    ((n : ℝ) - 2) * (Real.sin θ) ^ n := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  let b : ℝ := ((n : ℝ) + 2) / 2
  have hb : b + b - 2 = (n : ℝ) := by dsimp [b]; ring
  have hpowadd : Real.rpow (Real.sin θ) b *
      Real.rpow (Real.sin θ) b =
      Real.rpow (Real.sin θ) (b + b) :=
    (Real.rpow_add hs b b).symm
  have hpowsub : Real.rpow (Real.sin θ) (b + b) /
      (Real.sin θ) ^ 2 = (Real.sin θ) ^ n := by
    have htwo : Real.rpow (Real.sin θ) (2 : ℝ) =
        (Real.sin θ) ^ 2 := Real.rpow_natCast _ 2
    calc
      _ = Real.rpow (Real.sin θ) (b + b) /
            Real.rpow (Real.sin θ) (2 : ℝ) := by rw [htwo]
      _ = Real.rpow (Real.sin θ) (b + b - 2) :=
        (Real.rpow_sub hs (b + b) 2).symm
      _ = Real.rpow (Real.sin θ) (n : ℝ) := by rw [hb]
      _ = (Real.sin θ) ^ n := Real.rpow_natCast _ _
  change (((n : ℝ) - 2) / (Real.sin θ) ^ 2) *
      Real.rpow (Real.sin θ) b * Real.rpow (Real.sin θ) b =
    ((n : ℝ) - 2) * (Real.sin θ) ^ n
  calc
    _ = ((n : ℝ) - 2) *
          (Real.rpow (Real.sin θ) b * Real.rpow (Real.sin θ) b) /
          (Real.sin θ) ^ 2 := by ring
    _ = ((n : ℝ) - 2) *
          (Real.rpow (Real.sin θ) (b + b) / (Real.sin θ) ^ 2) := by
      rw [hpowadd]
      ring
    _ = ((n : ℝ) - 2) * (Real.sin θ) ^ n := by rw [hpowsub]

private theorem positiveTest_potential_Ioc
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) Real.pi) :
    angularPotential n θ * (positiveTestState n).g θ *
      (positiveTestState n).g θ =
    ((n : ℝ) - 2) * (Real.sin θ) ^ n := by
  by_cases hπ : θ = Real.pi
  · subst θ
    have hb : (((n : ℝ) + 2) / 2) ≠ 0 := by positivity
    have hn0 : n ≠ 0 := by omega
    simp [angularPotential, positiveTestState, positiveTestG,
      Real.sin_pi, Real.zero_rpow hb, hn0]
  · exact positiveTest_potential_interior n θ
      ⟨hθ.1, lt_of_le_of_ne hθ.2 hπ⟩

private theorem positiveTest_derivative_sq_Ioc
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) Real.pi) :
    angularDerivative n (positiveTestState n) θ *
      angularDerivative n (positiveTestState n) θ =
    (((n : ℝ) + 2) / 2) ^ 2 *
      (Real.sin θ) ^ n * (Real.cos θ) ^ 2 := by
  have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ.1.le, hθ.2⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
  have hnr : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hsum : (n : ℝ) / 2 + (n : ℝ) / 2 = (n : ℝ) := by ring
  have hpow :
      Real.rpow (Real.sin θ) ((n : ℝ) / 2) *
        Real.rpow (Real.sin θ) ((n : ℝ) / 2) =
      (Real.sin θ) ^ n := by
    calc
      _ = Real.rpow (Real.sin θ)
          ((n : ℝ) / 2 + (n : ℝ) / 2) :=
        (Real.rpow_add_of_nonneg hs hnr hnr).symm
      _ = Real.rpow (Real.sin θ) (n : ℝ) := by rw [hsum]
      _ = (Real.sin θ) ^ n := Real.rpow_natCast _ _
  rw [positiveTest_angularDerivative_Ioc n hn θ hθ]
  calc
    _ = (((n : ℝ) + 2) / 2) ^ 2 *
          (Real.rpow (Real.sin θ) ((n : ℝ) / 2) *
            Real.rpow (Real.sin θ) ((n : ℝ) / 2)) *
          (Real.cos θ) ^ 2 := by ring
    _ = (((n : ℝ) + 2) / 2) ^ 2 *
          (Real.sin θ) ^ n * (Real.cos θ) ^ 2 := by rw [hpow]

/-- The full original self-energy of the concrete positive test is finite.
This is the additional input needed to polarize the original weak form. -/
theorem positiveTest_self_energy_integrable
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ *
        (angularDerivative n (positiveTestState n) θ *
            angularDerivative n (positiveTestState n) θ +
          angularPotential n θ * (positiveTestState n).g θ *
            (positiveTestState n).g θ))
      volume (0 : ℝ) Real.pi := by
  have hnr : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have hnr' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwc : Continuous (angularWeight n r) := by
    unfold angularWeight
    exact ((Real.continuous_rpow_const hnr).comp Real.continuous_sin).mul
      (Real.continuous_exp.comp
        ((continuous_const.mul Real.continuous_cos)))
  have hc : Continuous (fun θ : ℝ =>
      angularWeight n r θ *
        (((((n : ℝ) + 2) / 2) ^ 2 *
            (Real.sin θ) ^ n * (Real.cos θ) ^ 2) +
          ((n : ℝ) - 2) * (Real.sin θ) ^ n)) := by
    exact hwc.mul (by fun_prop)
  have hi : IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ *
        (((((n : ℝ) + 2) / 2) ^ 2 *
            (Real.sin θ) ^ n * (Real.cos θ) ^ 2) +
          ((n : ℝ) - 2) * (Real.sin θ) ^ n))
      volume (0 : ℝ) Real.pi := hc.intervalIntegrable _ _
  apply hi.congr
  intro θ hθ
  have hθ' : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
  change angularWeight n r θ *
      (((((n : ℝ) + 2) / 2) ^ 2 *
          (Real.sin θ) ^ n * (Real.cos θ) ^ 2) +
        ((n : ℝ) - 2) * (Real.sin θ) ^ n) =
    angularWeight n r θ *
      (angularDerivative n (positiveTestState n) θ *
          angularDerivative n (positiveTestState n) θ +
        angularPotential n θ * (positiveTestState n).g θ *
          (positiveTestState n).g θ)
  rw [positiveTest_derivative_sq_Ioc n hn θ hθ',
    positiveTest_potential_Ioc n hn θ hθ']

end

end DFL.GCI
