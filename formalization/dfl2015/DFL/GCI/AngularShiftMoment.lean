import DFL.GCI.AngularSineEnergy

/-!
# All-dimensional angular-to-marginal shift moments

The forcing law `angularWeight_n(θ) sin²θ dθ` pushes under `t=cosθ`
to the original first-coordinate marginal in ambient dimension `n+2`.
These identities use the unmodified original marginal integrals.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private theorem shiftedMarginalWeight_continuous
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    Continuous (DFL.marginalWeight (n + 2) r) := by
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : Continuous (fun t : ℝ =>
      (1 - t ^ 2) ^ (((n : ℝ) - 1) / 2)) :=
    (Real.continuous_rpow_const hexp).comp (by fun_prop)
  have h := (by fun_prop : Continuous (fun t : ℝ =>
    Real.exp (r * t))).mul hpow
  convert h using 1
  ext t
  simp only [DFL.marginalWeight]
  congr 2
  push_cast
  ring

private theorem shiftedMarginalWeight_cos
    (n : ℕ) (hn : 2 ≤ n) (r θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    DFL.marginalWeight (n + 2) r (Real.cos θ) =
      Real.exp (r * Real.cos θ) *
        (Real.sin θ) ^ (n - 1) := by
  have hsq : 1 - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hroot :
      ((Real.sin θ) ^ (2 : ℕ)) ^ (((n : ℝ) - 1) / 2) =
        (Real.sin θ) ^ (n - 1) := by
    have hsquare : (Real.sin θ) ^ (2 : ℕ) =
        (Real.sin θ) ^ (2 : ℝ) :=
      (Real.rpow_natCast (Real.sin θ) 2).symm
    rw [hsquare, ← Real.rpow_mul hs]
    have hexp : (2 : ℝ) * (((n : ℝ) - 1) / 2) =
        ((n - 1 : ℕ) : ℝ) := by rw [← hcast]; ring
    rw [hexp, Real.rpow_natCast]
  unfold DFL.marginalWeight
  have hexp : (((n + 2 : ℕ) : ℝ) - 3) / 2 =
      ((n : ℝ) - 1) / 2 := by push_cast; ring
  rw [hexp, hsq]
  exact congrArg (fun x : ℝ => Real.exp (r * Real.cos θ) * x) hroot

private theorem cos_integral_transport
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ θ in (0 : ℝ)..Real.pi, g (Real.cos θ) * Real.sin θ) =
      ∫ t in (-1 : ℝ)..1, g t := by
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos)
    (f' := fun θ => -Real.sin θ) (g := g)
    (fun θ _ => Real.hasDerivAt_cos θ)
    (by fun_prop : Continuous (fun θ : ℝ => -Real.sin θ)).continuousOn
    hg
  have hchange' :
      (∫ θ in (0 : ℝ)..Real.pi,
        g (Real.cos θ) * (-Real.sin θ)) =
          ∫ t in (1 : ℝ)..(-1 : ℝ), g t := by
    simpa only [Function.comp_apply, Real.cos_zero, Real.cos_pi]
      using hchange
  calc
    (∫ θ in (0 : ℝ)..Real.pi,
      g (Real.cos θ) * Real.sin θ) =
        -(∫ θ in (0 : ℝ)..Real.pi,
          g (Real.cos θ) * (-Real.sin θ)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = -(∫ t in (1 : ℝ)..(-1 : ℝ), g t) := by rw [hchange']
    _ = ∫ t in (-1 : ℝ)..1, g t := by
      rw [intervalIntegral.integral_symm]
      ring

private theorem sin_pow_shift (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    (Real.sin θ) ^ (n - 2) * (Real.sin θ) ^ 2 =
      (Real.sin θ) ^ (n - 1) * Real.sin θ := by
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rw [hn1, pow_succ]
  ring

/-- The forcing norm in ambient dimension `n` is exactly the original
marginal partition function in ambient dimension `n+2`. -/
theorem originalForcingNorm_eq_shifted_partition
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    originalForcingNorm n r = DFL.partition (n + 2) r := by
  have hchange :
      (∫ θ in (0 : ℝ)..Real.pi,
        DFL.marginalWeight (n + 2) r (Real.cos θ) * Real.sin θ) =
          DFL.partition (n + 2) r := by
    simpa only [DFL.partition] using
      cos_integral_transport (DFL.marginalWeight (n + 2) r)
        (shiftedMarginalWeight_continuous n hn r)
  calc
    originalForcingNorm n r =
        ∫ θ in (0 : ℝ)..Real.pi,
          DFL.marginalWeight (n + 2) r (Real.cos θ) * Real.sin θ := by
      unfold originalForcingNorm
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [angularWeight_eq_sin_pow n hn r θ,
        shiftedMarginalWeight_cos n hn r θ hθ']
      calc
        _ = ((Real.sin θ) ^ (n - 2) * (Real.sin θ) ^ 2) *
              Real.exp (r * Real.cos θ) := by ring
        _ = ((Real.sin θ) ^ (n - 1) * Real.sin θ) *
              Real.exp (r * Real.cos θ) := by
          rw [sin_pow_shift n hn θ]
        _ = _ := by ring
    _ = DFL.partition (n + 2) r := hchange

/-- The corresponding angular cosine moment is the original shifted
marginal first moment, with no normalization hidden. -/
theorem originalShiftMoment_eq_shifted_firstMoment
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    originalShiftMoment n r = DFL.firstMoment (n + 2) r := by
  have hcont : Continuous
      (fun t : ℝ => t * DFL.marginalWeight (n + 2) r t) :=
    continuous_id.mul (shiftedMarginalWeight_continuous n hn r)
  have hchange :
      (∫ θ in (0 : ℝ)..Real.pi,
        (Real.cos θ * DFL.marginalWeight (n + 2) r (Real.cos θ)) *
          Real.sin θ) = DFL.firstMoment (n + 2) r := by
    simpa only [DFL.firstMoment] using
      cos_integral_transport
        (fun t : ℝ => t * DFL.marginalWeight (n + 2) r t) hcont
  calc
    originalShiftMoment n r =
        ∫ θ in (0 : ℝ)..Real.pi,
          (Real.cos θ * DFL.marginalWeight (n + 2) r (Real.cos θ)) *
            Real.sin θ := by
      unfold originalShiftMoment
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [angularWeight_eq_sin_pow n hn r θ,
        shiftedMarginalWeight_cos n hn r θ hθ']
      calc
        _ = ((Real.sin θ) ^ (n - 2) * (Real.sin θ) ^ 2) *
              (Real.exp (r * Real.cos θ) * Real.cos θ) := by ring
        _ = ((Real.sin θ) ^ (n - 1) * Real.sin θ) *
              (Real.exp (r * Real.cos θ) * Real.cos θ) := by
          rw [sin_pow_shift n hn θ]
        _ = _ := by ring
    _ = DFL.firstMoment (n + 2) r := hchange

/-- The normalized original angular shift moment is precisely the
orientation mean two ambient dimensions higher. -/
theorem orientationMean_shift_eq_angular_shift_ratio
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    DFL.orientationMean (n + 2) r =
      originalShiftMoment n r / originalForcingNorm n r := by
  rw [DFL.orientationMean,
    ← originalShiftMoment_eq_shifted_firstMoment n hn r,
    ← originalForcingNorm_eq_shifted_partition n hn r]

end

end DFL.GCI
