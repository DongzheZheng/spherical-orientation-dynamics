import Mathlib

/-!
# Logarithmic derivative of the density curve

This is the calculus bridge in `hysteresis.tex`, equation
`hyst:joint-relations`: the derivative of `R = j / c` has the sign of the
difference between the elasticities of feedback and spherical mean.
The theorem is deliberately stated for two differentiable functions.  Its
eventual use with the original von Mises--Fisher mean requires separate
proofs of differentiability and positivity for that exact integral.
-/

namespace DFL.Hysteresis

noncomputable def densityCurve (j c : ℝ → ℝ) (r : ℝ) : ℝ := j r / c r

theorem densityCurve_log_deriv (j c : ℝ → ℝ) (r : ℝ)
    (hj : DifferentiableAt ℝ j r) (hc : DifferentiableAt ℝ c r)
    (hj0 : j r ≠ 0) (hc0 : c r ≠ 0) :
    deriv (densityCurve j c) r / densityCurve j c r =
      deriv j r / j r - deriv c r / c r := by
  have hdiv : HasDerivAt (fun x => j x / c x)
      ((deriv j r * c r - j r * deriv c r) / (c r) ^ 2) r :=
    hj.hasDerivAt.div hc.hasDerivAt hc0
  have hderiv : deriv (densityCurve j c) r =
      (deriv j r * c r - j r * deriv c r) / (c r) ^ 2 := by
    exact hdiv.deriv
  rw [hderiv]
  unfold densityCurve
  field_simp [hj0, hc0]

theorem densityCurve_sign (j c : ℝ → ℝ) (r : ℝ)
    (hj : DifferentiableAt ℝ j r) (hc : DifferentiableAt ℝ c r)
    (hjpos : 0 < j r) (hcpos : 0 < c r) (hr : 0 < r) :
    (0 < deriv (densityCurve j c) r ↔
      r * deriv c r / c r < r * deriv j r / j r) := by
  have hlog := densityCurve_log_deriv j c r hj hc (ne_of_gt hjpos) (ne_of_gt hcpos)
  have hRpos : 0 < densityCurve j c r := div_pos hjpos hcpos
  have heq : r * (deriv j r / j r - deriv c r / c r) =
      r * deriv j r / j r - r * deriv c r / c r := by ring
  constructor
  · intro h
    have hlogpos : 0 < deriv (densityCurve j c) r / densityCurve j c r :=
      div_pos h hRpos
    rw [hlog] at hlogpos
    have hscaled := mul_pos hr hlogpos
    rw [heq] at hscaled
    linarith
  · intro h
    have hscaled : 0 < r * (deriv j r / j r - deriv c r / c r) := by
      rw [heq]
      linarith
    have hgap : 0 < deriv j r / j r - deriv c r / c r :=
      (mul_pos_iff_of_pos_left hr).mp hscaled
    rw [← hlog] at hgap
    exact (div_pos_iff_of_pos_right hRpos).mp hgap

end DFL.Hysteresis
