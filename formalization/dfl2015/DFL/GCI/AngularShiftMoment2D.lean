import DFL.GCI.AngularUpper2D

/-!
# Angular and marginal moments in the two-dimensional GCI comparison

The angular sine-squared weight is the first-coordinate marginal in ambient
dimension four.  These are exact equalities of the original integrals, with
their normalizations fixed by the change of variables `t = cos θ`.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private theorem marginalWeight_four_continuous (r : ℝ) :
    Continuous (DFL.marginalWeight 4 r) := by
  have hpow : Continuous (fun t : ℝ =>
      (1 - t ^ 2) ^ (1 / (2 : ℝ))) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  have h := (by fun_prop : Continuous (fun t : ℝ => Real.exp (r * t))).mul hpow
  unfold DFL.marginalWeight
  convert h using 1
  ext t
  norm_num

private theorem marginalWeight_four_cos (r θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    DFL.marginalWeight 4 r (Real.cos θ) =
      Real.exp (r * Real.cos θ) * Real.sin θ := by
  have hsq : 1 - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hroot : (1 - (Real.cos θ) ^ 2) ^ (1 / (2 : ℝ)) = Real.sin θ := by
    rw [← Real.sqrt_eq_rpow, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin]
  simpa [DFL.marginalWeight,
    show (((4 : ℝ) - 3) / 2) = (1 / (2 : ℝ)) by norm_num, one_div]
    using congrArg (fun x : ℝ => Real.exp (r * Real.cos θ) * x) hroot

/-- Orientation-reversing change of variables `t = cos θ`, for a continuous
integrand on the real line. -/
private theorem cos_integral_transport (g : ℝ → ℝ) (hg : Continuous g) :
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
    simpa only [Function.comp_apply, Real.cos_zero, Real.cos_pi] using hchange
  calc
    (∫ θ in (0 : ℝ)..Real.pi, g (Real.cos θ) * Real.sin θ) =
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

/-- The angular forcing norm equals the exact dimension-four marginal
partition function. -/
theorem originalForcingNorm_two_eq_partition_four (r : ℝ) :
    originalForcingNorm 2 r = DFL.partition 4 r := by
  have hchange :
      (∫ θ in (0 : ℝ)..Real.pi,
        DFL.marginalWeight 4 r (Real.cos θ) * Real.sin θ) =
          DFL.partition 4 r := by
    simpa only [DFL.partition] using
      cos_integral_transport (DFL.marginalWeight 4 r)
        (marginalWeight_four_continuous r)
  calc
    originalForcingNorm 2 r =
        ∫ θ in (0 : ℝ)..Real.pi,
          DFL.marginalWeight 4 r (Real.cos θ) * Real.sin θ := by
      unfold originalForcingNorm
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [twoD_angularWeight, marginalWeight_four_cos r θ hθ']
      ring
    _ = DFL.partition 4 r := hchange

/-- The shifted angular cosine moment equals the exact dimension-four
marginal first moment. -/
theorem twoDShiftMoment_eq_firstMoment_four (r : ℝ) :
    twoDShiftMoment r = DFL.firstMoment 4 r := by
  have hcont : Continuous (fun t : ℝ => t * DFL.marginalWeight 4 r t) :=
    continuous_id.mul (marginalWeight_four_continuous r)
  have hchange :
      (∫ θ in (0 : ℝ)..Real.pi,
        (Real.cos θ * DFL.marginalWeight 4 r (Real.cos θ)) *
          Real.sin θ) = DFL.firstMoment 4 r := by
    simpa only [DFL.firstMoment] using
      cos_integral_transport
        (fun t : ℝ => t * DFL.marginalWeight 4 r t) hcont
  calc
    twoDShiftMoment r =
        ∫ θ in (0 : ℝ)..Real.pi,
          (Real.cos θ * DFL.marginalWeight 4 r (Real.cos θ)) *
            Real.sin θ := by
      unfold twoDShiftMoment
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [marginalWeight_four_cos r θ hθ']
      ring
    _ = DFL.firstMoment 4 r := hchange

/-- The physical angular shift moment is precisely the original
dimension-four orientation mean after normalization. -/
theorem orientationMean_four_eq_twoD_shift_ratio (r : ℝ) :
    DFL.orientationMean 4 r =
      twoDShiftMoment r / originalForcingNorm 2 r := by
  rw [DFL.orientationMean, ← twoDShiftMoment_eq_firstMoment_four,
    ← originalForcingNorm_two_eq_partition_four]

end

end DFL.GCI
