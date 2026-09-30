import DFL.Hysteresis.OriginalRiccati
import DFL.Hysteresis.ZeroDirectionODE
import DFL.Hysteresis.TargetBridge
import DFL.Hysteresis.FeedbackDerivative

/-!
# The original spherical mean in the zero-direction scalar equation

This module identifies the positive quadratic root with `r * orientationMean`
and derives the scalar ODE for the elasticity difference from the original
marginal.  It contains no new Riccati assumption.
-/

namespace DFL.Hysteresis.OriginalTrajectory

open Set Filter
open scoped Topology
open DFL.Hysteresis.ElasticityODE
open DFL.Hysteresis.ZeroDirectionODE

noncomputable def H (n : ℕ) (r : ℝ) : ℝ :=
  a r - elasticity (DFL.orientationMean n) r

private theorem positive_root_eq {r y m : ℝ} (hr : 0 < r) (hy : 0 < y)
    (hroot : y * (y + m) = r ^ 2) :
    (Real.sqrt (m ^ 2 + 4 * r ^ 2) - m) / 2 = y := by
  have hym : 0 < y + m := by
    by_contra h
    have hle : y + m ≤ 0 := le_of_not_gt h
    have hprod : y * (y + m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hy) hle
    nlinarith [sq_pos_of_pos hr]
  have htwoy : 0 ≤ 2 * y + m := by linarith
  have hsq : m ^ 2 + 4 * r ^ 2 = (2 * y + m) ^ 2 := by
    nlinarith [hroot]
  rw [hsq, Real.sqrt_sq htwoy]
  ring

/-- The quadratic positive root in the paper is exactly the scaled original
spherical mean, at every positive field and in every dimension `n ≥ 2`. -/
theorem original_scaledMean_eq_Y (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    scaledMean (DFL.orientationMean n) r =
      Y n r (elasticity (DFL.orientationMean n) r) := by
  let y := scaledMean (DFL.orientationMean n) r
  let m := (n : ℝ) - 1 + elasticity (DFL.orientationMean n) r
  have hy : 0 < y := scaledMean_pos (DFL.orientationMean n) hr
    (DFL.orientationMean_pos n hn hr)
  have hroot : y * (y + m) = r ^ 2 := by
    simpa only [y, m, add_assoc, add_comm, add_left_comm] using
      scaledMean_quadratic n (DFL.orientationMean n) hr
        (DFL.orientationMean_pos n hn hr)
        (DFL.orientationMean_differentiableAt n hn r)
        (DFL.orientationMean_riccati n hn hr)
  unfold Y
  simpa only [y, m] using (positive_root_eq hr hy hroot).symm

private theorem original_elasticity_differentiableAt (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (elasticity (DFL.orientationMean n)) r := by
  let c := DFL.orientationMean n
  let g : ℝ → ℝ := fun x => x / c x - ((n : ℝ) - 1) - x * c x
  have hlocal : elasticity c =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact elasticity_eq n c hx (DFL.orientationMean_pos n hn hx)
      (DFL.orientationMean_differentiableAt n hn x)
      (DFL.orientationMean_riccati n hn hx)
  have hc : DifferentiableAt ℝ c r := DFL.orientationMean_differentiableAt n hn r
  have hcne : c r ≠ 0 := ne_of_gt (DFL.orientationMean_pos n hn hr)
  have hg : DifferentiableAt ℝ g r := by
    dsimp [g]
    exact ((differentiableAt_id.div hc hcne).sub
      (differentiableAt_const ((n : ℝ) - 1))).sub
      (differentiableAt_id.mul hc)
  exact hg.congr_of_eventuallyEq hlocal

private theorem a_differentiableAt {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ a r := by
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have hden : 2 * chi r ≠ 0 := by positivity
  unfold a
  exact ((chi_hasDerivAt hr).add_const 1).div
    ((chi_hasDerivAt hr).const_mul 2) hden |>.differentiableAt

/-- The elasticity difference of the original spherical mean obeys exactly
the scalar equation used in the zero-direction and crossing argument. -/
theorem original_H_ode (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    deriv (H n) r = F n r (H n r) := by
  let e := elasticity (DFL.orientationMean n)
  have ha : DifferentiableAt ℝ a r := a_differentiableAt hr
  have he : DifferentiableAt ℝ e r := original_elasticity_differentiableAt n hn hr
  have hH : deriv (H n) r = deriv a r - deriv e r := by
    change deriv (fun x => a x - e x) r = deriv a r - deriv e r
    exact deriv_sub ha he
  have heode : r * deriv e r =
      ((n : ℝ) - 1 + e r) * (1 - e r) -
        2 * e r * scaledMean (DFL.orientationMean n) r :=
    DFL.orientationMean_elasticity_ode n hn hr
  have hederiv : deriv e r =
      (((n : ℝ) - 1 + e r) * (1 - e r) -
        2 * e r * scaledMean (DFL.orientationMean n) r) / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    simpa only [mul_comm] using heode
  have hadd : a r - H n r = e r := by
    unfold H e
    ring
  have hm : (n : ℝ) - 1 + a r - H n r = (n : ℝ) - 1 + e r := by
    rw [← hadd]
    ring
  have hone : 1 - a r + H n r = 1 - e r := by
    rw [← hadd]
    ring
  have hF : F n r (H n r) = deriv a r -
      (1 / r) *
        (((n : ℝ) - 1 + e r) * (1 - e r) -
          2 * e r * scaledMean (DFL.orientationMean n) r) := by
    unfold F
    rw [hm, hone, hadd, ← original_scaledMean_eq_Y n hn hr]
  rw [hH, hF, hederiv]
  ring

/-- Exact slope identity for the original positive-field equilibrium curve.
The sign of its derivative is the sign of the original elasticity difference
because both `r` and the curve are positive. -/
theorem original_density_slope (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    r * deriv (DFL.equilibriumDensity n) r =
      DFL.equilibriumDensity n r * H n r := by
  have hc : DifferentiableAt ℝ (DFL.orientationMean n) r :=
    DFL.orientationMean_differentiableAt n hn r
  have hj : DifferentiableAt ℝ DFL.inverseAlignment r :=
    (DFL.Hysteresis.inverseFeedback_hasDerivAt hr).differentiableAt
  have hcne : DFL.orientationMean n r ≠ 0 :=
    ne_of_gt (DFL.orientationMean_pos n hn hr)
  have hjne : DFL.inverseAlignment r ≠ 0 :=
    ne_of_gt (DFL.Hysteresis.inverseFeedback_pos hr)
  have hRne : DFL.equilibriumDensity n r ≠ 0 :=
    ne_of_gt (DFL.Hysteresis.equilibriumDensity_pos n hn hr)
  have hlog := DFL.Hysteresis.original_curve_log_deriv n r hj hc hjne hcne
  have haeq : r * deriv DFL.inverseAlignment r / DFL.inverseAlignment r = a r := by
    change r * deriv DFL.Hysteresis.inverseFeedback r /
      DFL.Hysteresis.inverseFeedback r = a r
    rw [DFL.Hysteresis.inverseFeedback_elasticity hr]
    have hs : Real.sqrt (1 + 4 * r) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by linarith))
    unfold a chi
    field_simp [hs]
  have hH : H n r = r *
      (deriv DFL.inverseAlignment r / DFL.inverseAlignment r -
        deriv (DFL.orientationMean n) r / DFL.orientationMean n r) := by
    unfold H ElasticityODE.elasticity
    rw [← haeq]
    ring
  have hratio :
      (r * deriv (DFL.equilibriumDensity n) r) /
        DFL.equilibriumDensity n r = H n r := by
    calc
      (r * deriv (DFL.equilibriumDensity n) r) /
          DFL.equilibriumDensity n r =
        r * (deriv (DFL.equilibriumDensity n) r /
          DFL.equilibriumDensity n r) := by ring
      _ = r * (deriv DFL.inverseAlignment r / DFL.inverseAlignment r -
            deriv (DFL.orientationMean n) r / DFL.orientationMean n r) := by
          rw [hlog]
      _ = H n r := hH.symm
  exact (div_eq_iff hRne).mp hratio |>.trans (mul_comm _ _)

end DFL.Hysteresis.OriginalTrajectory
