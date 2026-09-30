import DFL.Hysteresis.Feedback

/-!
# The original feedback elasticity

The theorems concern the explicit inverse of the original law `J ↦ J + J²`
for positive field strength.  They formalize the `j` and `a` part of equation
`hyst:elasticities` in the manuscript; the spherical mean is not used here.
-/

namespace DFL.Hysteresis

/-- The derivative of the nonnegative inverse feedback law, for `r > 0`. -/
theorem inverseFeedback_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt inverseFeedback (1 / Real.sqrt (1 + 4 * r)) r := by
  have harg : 1 + 4 * r ≠ 0 := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 + 4 * x) 4 r := by
    convert (hasDerivAt_const r (1 : ℝ)).add
      ((hasDerivAt_id r).const_mul 4) using 1
    ring
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 + 4 * x))
      (4 / (2 * Real.sqrt (1 + 4 * r))) r := hlin.sqrt harg
  have hformula : HasDerivAt inverseFeedback
      ((4 / (2 * Real.sqrt (1 + 4 * r))) / 2) r := by
    convert (hsqrt.sub_const 1).div_const 2 using 1
  convert hformula using 1
  field_simp
  ring

/-- Exact derivative of the original inverse feedback law. -/
theorem inverseFeedback_deriv {r : ℝ} (hr : 0 < r) :
    deriv inverseFeedback r = 1 / Real.sqrt (1 + 4 * r) :=
  (inverseFeedback_hasDerivAt hr).deriv

/-- The feedback elasticity `a(r) = r j'(r) / j(r)` in the DFL paper. -/
theorem inverseFeedback_elasticity {r : ℝ} (hr : 0 < r) :
    r * deriv inverseFeedback r / inverseFeedback r =
      (1 : ℝ) / 2 + 1 / (2 * Real.sqrt (1 + 4 * r)) := by
  let s : ℝ := Real.sqrt (1 + 4 * r)
  have harg : 0 ≤ 1 + 4 * r := by linarith
  have hsq : s ^ 2 = 1 + 4 * r := Real.sq_sqrt harg
  have hsnonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hsone : 1 < s := by nlinarith
  have hsnz : s ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hsone)
  have hsubnz : s - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hsone)
  rw [inverseFeedback_deriv hr]
  change r * (1 / s) / ((s - 1) / 2) = (1 : ℝ) / 2 + 1 / (2 * s)
  field_simp
  nlinarith [hsq]

end DFL.Hysteresis
