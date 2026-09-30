import DFL.GCI.AngularMomentGeneral

/-!
# Endpoint regularity for the remaining ambient dimension three

Here the angular flux contains `sqrt(sin θ)`.  Its derivative is singular
at both endpoints but integrable.  The first bridge below proves exactly
that integrability by changing variables on the two monotone halves of
the sine map.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private def threeDSingularDerivative (θ : ℝ) : ℝ :=
  Real.sin θ ^ (-(1 / 2 : ℝ)) * Real.cos θ

theorem threeD_singular_derivative_integrable :
    IntervalIntegrable threeDSingularDerivative volume
      (0 : ℝ) Real.pi := by
  have hleft : IntervalIntegrable threeDSingularDerivative volume
      (0 : ℝ) (Real.pi / 2) := by
    have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := Real.sin) (f' := Real.cos)
      (g := fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
      (a := (0 : ℝ)) (b := Real.pi / 2)
      Real.continuous_sin.continuousOn
      (by intro x _; exact Real.hasDerivAt_sin x)
      (by
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          simpa [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
            max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx'.1, Real.pi_pos], hx'.2.le⟩)
    change IntervalIntegrable
      (fun θ : ℝ => ((fun t : ℝ => t ^ (-(1 / 2 : ℝ))) ∘ Real.sin) θ * Real.cos θ)
      volume 0 (Real.pi / 2)
    apply hsub.2
    simpa [Real.sin_zero, Real.sin_pi_div_two] using
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))
  have hright : IntervalIntegrable threeDSingularDerivative volume
      (Real.pi / 2) Real.pi := by
    have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
      (f := Real.sin) (f' := Real.cos)
      (g := fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
      (a := Real.pi / 2) (b := Real.pi)
      Real.continuous_sin.continuousOn
      (by intro x _; exact Real.hasDerivAt_sin x)
      (by
        intro x hx
        have hx' : x ∈ Set.Ioo (Real.pi / 2) Real.pi := by
          simpa [min_eq_left (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi),
            max_eq_right (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)] using hx
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hx'.1.le
          (by linarith [hx'.2, Real.pi_pos]))
    change IntervalIntegrable
      (fun θ : ℝ => ((fun t : ℝ => t ^ (-(1 / 2 : ℝ))) ∘ Real.sin) θ * Real.cos θ)
      volume (Real.pi / 2) Real.pi
    apply hsub.2
    simpa [Real.sin_pi_div_two, Real.sin_pi] using
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (1 : ℝ)) (b := (0 : ℝ))
        (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))
  exact hleft.trans hright

end

end DFL.GCI
