import DFL.Targets
import DFL.Hysteresis.Feedback
import DFL.Hysteresis.Elasticity
import DFL.Hysteresis.Marginal

/-!
# Exact target bridges for the hysteresis algebra

The auxiliary feedback and quotient-calculus modules are connected here to
the definitions built from the original von Mises--Fisher marginal.  These
bridges are definitional equalities only; they do not supply the outstanding
analytic properties of that marginal.
-/

namespace DFL.Hysteresis

theorem inverseAlignment_eq_inverseFeedback (r : ℝ) :
    DFL.inverseAlignment r = inverseFeedback r := by
  rfl

theorem equilibriumDensity_eq_densityCurve (n : ℕ) (r : ℝ) :
    DFL.equilibriumDensity n r =
      densityCurve DFL.inverseAlignment (DFL.orientationMean n) r := by
  rfl

/-- The original equilibrium density curve is positive on the physical
positive-field range in every embedding dimension `n ≥ 2`. -/
theorem equilibriumDensity_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < DFL.equilibriumDensity n r := by
  have hj : 0 < DFL.inverseAlignment r := by
    rw [inverseAlignment_eq_inverseFeedback]
    exact inverseFeedback_pos hr
  exact div_pos hj (DFL.orientationMean_pos n hn hr)

/-- The logarithmic-derivative identity for the actual density-curve
definition.  The as-yet-unproved analytic inputs about the spherical mean
are visible in the theorem's hypotheses. -/
theorem original_curve_log_deriv (n : ℕ) (r : ℝ)
    (hj : DifferentiableAt ℝ DFL.inverseAlignment r)
    (hc : DifferentiableAt ℝ (DFL.orientationMean n) r)
    (hj0 : DFL.inverseAlignment r ≠ 0)
    (hc0 : DFL.orientationMean n r ≠ 0) :
    deriv (DFL.equilibriumDensity n) r / DFL.equilibriumDensity n r =
      deriv DFL.inverseAlignment r / DFL.inverseAlignment r -
        deriv (DFL.orientationMean n) r / DFL.orientationMean n r := by
  exact densityCurve_log_deriv DFL.inverseAlignment
    (DFL.orientationMean n) r hj hc hj0 hc0

/-- For the actual DFL curve, positive slope is exactly the inequality
between the feedback and spherical-mean elasticities. -/
theorem original_curve_positive_slope_iff (n : ℕ) (r : ℝ)
    (hj : DifferentiableAt ℝ DFL.inverseAlignment r)
    (hc : DifferentiableAt ℝ (DFL.orientationMean n) r)
    (hjpos : 0 < DFL.inverseAlignment r)
    (hcpos : 0 < DFL.orientationMean n r) (hr : 0 < r) :
    (0 < deriv (DFL.equilibriumDensity n) r ↔
      r * deriv (DFL.orientationMean n) r / DFL.orientationMean n r <
        r * deriv DFL.inverseAlignment r / DFL.inverseAlignment r) := by
  exact densityCurve_sign DFL.inverseAlignment
    (DFL.orientationMean n) r hj hc hjpos hcpos hr

end DFL.Hysteresis
