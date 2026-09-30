import Mathlib

/-!
# Algebraic and differential consequences of the DFL mean Riccati identity

The Riccati equation is an explicit hypothesis.  This module does not derive
it from the normalized von Mises--Fisher sphere integral.  The paper's
`n - 1` is represented in `ℝ`, so there is no truncated natural subtraction.
-/

namespace DFL.Hysteresis.ElasticityODE

open Set Filter
open scoped Topology

/-- The mean elasticity `e(r) = r c'(r) / c(r)`. -/
noncomputable def elasticity (c : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv c r / c r

/-- The scaled mean `y(r) = r c(r)`. -/
def scaledMean (c : ℝ → ℝ) (r : ℝ) : ℝ := r * c r

/-- The original Riccati identity for the spherical mean, stated as an input. -/
def RiccatiAt (n : ℕ) (c : ℝ → ℝ) (r : ℝ) : Prop :=
  deriv c r = 1 - ((n : ℝ) - 1) * c r / r - (c r) ^ 2

theorem scaledMean_pos (c : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hc : 0 < c r) : 0 < scaledMean c r := by
  exact mul_pos hr hc

/-- The first algebraic identity in `hyst:joint-relations`. -/
theorem elasticity_eq (n : ℕ) (c : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hc : 0 < c r)
    (_hdiff : DifferentiableAt ℝ c r) (hric : RiccatiAt n c r) :
    elasticity c r = r / c r - ((n : ℝ) - 1) - scaledMean c r := by
  change deriv c r = 1 - ((n : ℝ) - 1) * c r / r - (c r) ^ 2 at hric
  unfold elasticity scaledMean
  rw [hric]
  field_simp

/-- The positive-root quadratic relation uses the same `c` as the Riccati
input and the elasticity, as in `hyst:joint-relations`. -/
theorem scaledMean_quadratic (n : ℕ) (c : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hc : 0 < c r)
    (hdiff : DifferentiableAt ℝ c r) (hric : RiccatiAt n c r) :
    scaledMean c r * (scaledMean c r + ((n : ℝ) - 1) + elasticity c r) =
      r ^ 2 := by
  rw [elasticity_eq n c hr hc hdiff hric]
  unfold scaledMean
  field_simp
  ring

private noncomputable def algebraicElasticity (n : ℕ) (c : ℝ → ℝ) (r : ℝ) : ℝ :=
  r / c r - ((n : ℝ) - 1) - r * c r

/-- The differential equation `hyst:elasticity-ode`, provided the original
Riccati equation and regularity hold on the positive-field region.  No
second-derivative assumption is needed: Riccati expresses `e` locally using
only `c`, whose first derivative exists. -/
theorem elasticity_ode (n : ℕ) (c : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hregion : ∀ x : ℝ, 0 < x →
      0 < c x ∧ DifferentiableAt ℝ c x ∧ RiccatiAt n c x) :
    r * deriv (elasticity c) r =
      ((n : ℝ) - 1 + elasticity c r) * (1 - elasticity c r) -
        2 * elasticity c r * scaledMean c r := by
  obtain ⟨hcr, hdiffr, hricr⟩ := hregion r hr
  have hlocal : elasticity c =ᶠ[𝓝 r] algebraicElasticity n c := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    obtain ⟨hcx, hdiffx, hricx⟩ := hregion x hx
    exact elasticity_eq n c hx hcx hdiffx hricx
  have hcderiv := hdiffr.hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
  have hdiv := hid.div hcderiv (ne_of_gt hcr)
  have hmul := hid.mul hcderiv
  have halgebraic : HasDerivAt (algebraicElasticity n c)
      ((c r - r * deriv c r) / (c r) ^ 2 -
        (c r + r * deriv c r)) r := by
    unfold algebraicElasticity
    convert (hdiv.sub_const ((n : ℝ) - 1)).sub hmul using 1
    ring
  have hederiv : deriv (elasticity c) r =
      (c r - r * deriv c r) / (c r) ^ 2 -
        (c r + r * deriv c r) :=
    (halgebraic.congr_of_eventuallyEq hlocal).deriv
  rw [hederiv]
  change deriv c r = 1 - ((n : ℝ) - 1) * c r / r - (c r) ^ 2 at hricr
  unfold elasticity scaledMean
  rw [hricr]
  field_simp
  ring

end DFL.Hysteresis.ElasticityODE
