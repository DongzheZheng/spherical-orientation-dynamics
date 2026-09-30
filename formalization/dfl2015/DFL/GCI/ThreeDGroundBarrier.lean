import DFL.GCI.AngularSineTest

/-!
# An exact positive supersolution for the original three-dimensional angular GCI operator

This is a source-level differential calculation.  The profile is positive
inside the angular interval and its operator residual is strictly positive
for every `r > 0`.  The result does not assert the existence of a weak
solution or transport the pointwise inequality across singular endpoints.
-/

namespace DFL.GCI

noncomputable section

def threeDGroundProfile (r θ : ℝ) : ℝ :=
  Real.sin θ * Real.exp (-(r * Real.cos θ) / 4)

private theorem threeDGroundProfile_hasDerivAt (r θ : ℝ) :
    HasDerivAt (threeDGroundProfile r)
      (Real.exp (-(r * Real.cos θ) / 4) *
        (Real.cos θ + r / 4 * (Real.sin θ) ^ 2)) θ := by
  have harg : HasDerivAt
      (fun x : ℝ => -(r * Real.cos x) / 4)
      (r * Real.sin θ / 4) θ := by
    convert (((Real.hasDerivAt_cos θ).const_mul r).neg).div_const 4 using 1
    ring
  have hprod := (Real.hasDerivAt_sin θ).mul harg.exp
  convert hprod using 1
  ring

theorem threeDGroundProfile_deriv (r θ : ℝ) :
    deriv (threeDGroundProfile r) θ =
      Real.exp (-(r * Real.cos θ) / 4) *
        (Real.cos θ + r / 4 * (Real.sin θ) ^ 2) :=
  (threeDGroundProfile_hasDerivAt r θ).deriv

private theorem threeDGroundProfile_second_hasDerivAt (r θ : ℝ) :
    HasDerivAt (deriv (threeDGroundProfile r))
      (Real.exp (-(r * Real.cos θ) / 4) *
        (-(Real.sin θ) + 3 * r / 4 * Real.sin θ * Real.cos θ +
          r ^ 2 / 16 * (Real.sin θ) ^ 3)) θ := by
  have hfun : deriv (threeDGroundProfile r) =
      fun x : ℝ =>
        Real.exp (-(r * Real.cos x) / 4) *
          (Real.cos x + r / 4 * (Real.sin x) ^ 2) := by
    funext x
    exact threeDGroundProfile_deriv r x
  rw [hfun]
  have harg : HasDerivAt
      (fun x : ℝ => -(r * Real.cos x) / 4)
      (r * Real.sin θ / 4) θ := by
    convert (((Real.hasDerivAt_cos θ).const_mul r).neg).div_const 4 using 1
    ring
  have hinner : HasDerivAt
      (fun x : ℝ => Real.cos x + r / 4 * (Real.sin x) ^ 2)
      (-Real.sin θ + (r / 2) * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_cos θ).add
      ((Real.hasDerivAt_sin θ).pow 2 |>.const_mul (r / 4)) using 1
    ring
  convert (harg.exp.mul hinner) using 1
  ring

theorem threeDGroundProfile_second_deriv (r θ : ℝ) :
    deriv (deriv (threeDGroundProfile r)) θ =
      Real.exp (-(r * Real.cos θ) / 4) *
        (-(Real.sin θ) + 3 * r / 4 * Real.sin θ * Real.cos θ +
          r ^ 2 / 16 * (Real.sin θ) ^ 3) :=
  (threeDGroundProfile_second_hasDerivAt r θ).deriv

/-- Exact residual for the original `n = 3` angular operator, with no
amplitude change of variables or hidden weak-solution assumption. -/
theorem threeDGroundProfile_operator_residual
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularOperatorValue 3 r θ
        (threeDGroundProfile r θ)
        (deriv (threeDGroundProfile r) θ)
        (deriv (deriv (threeDGroundProfile r)) θ) -
      2 * threeDGroundProfile r θ =
    (3 * r ^ 2 / 16) * (Real.sin θ) ^ 3 *
      Real.exp (-(r * Real.cos θ) / 4) := by
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo hθ).ne'
  rw [threeDGroundProfile_deriv, threeDGroundProfile_second_deriv]
  unfold angularOperatorValue angularPotential threeDGroundProfile
  field_simp [hsin]
  linear_combination -64 * (Real.sin_sq_add_cos_sq θ)

/-- The original `n = 3` operator lies strictly above eigenvalue `2`
on a positive physical angular profile for every positive field. -/
theorem threeDGroundProfile_strict_supersolution
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    2 * threeDGroundProfile r θ <
      angularOperatorValue 3 r θ
        (threeDGroundProfile r θ)
        (deriv (threeDGroundProfile r) θ)
        (deriv (deriv (threeDGroundProfile r)) θ) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hres := threeDGroundProfile_operator_residual r θ hθ
  have hpos : 0 < (3 * r ^ 2 / 16) * (Real.sin θ) ^ 3 *
      Real.exp (-(r * Real.cos θ) / 4) := by positivity
  linarith

theorem threeDGroundProfile_pos
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    0 < threeDGroundProfile r θ := by
  unfold threeDGroundProfile
  exact mul_pos (Real.sin_pos_of_mem_Ioo hθ) (Real.exp_pos _)

end

end DFL.GCI
