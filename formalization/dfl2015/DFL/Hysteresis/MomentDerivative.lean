import DFL.Hysteresis.Marginal

/-!
# Parameter derivatives and the original spherical moments

The moment quotient identity is stated for the *same* original marginal as
`DFL.orientationMean`.  The hypotheses `Z' = M₁` and `M₁' = M₂` are visible:
they still require a dominated-differentiation proof for that marginal,
including the singular circle case.  No conclusion about the conjecture is
smuggled into either hypothesis.
-/

namespace DFL

open MeasureTheory
open scoped Interval

noncomputable def secondMoment (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, t ^ 2 * marginalWeight n r t

/-- The second moment of the same original marginal is integrable, including
the circle's square-root endpoint singularity. -/
theorem secondMoment_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ 2 * marginalWeight n r t)
      volume (-1 : ℝ) 1 := by
  have hb := marginalWeight_intervalIntegrable n hn r
  have hc : ContinuousOn (fun t : ℝ => t ^ 2)
      (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  simpa only [mul_comm] using hb.continuousOn_mul hc

theorem orientationMean_deriv_of_moment_derivs (n : ℕ) (r : ℝ)
    (hZ : HasDerivAt (partition n) (firstMoment n r) r)
    (hM : HasDerivAt (firstMoment n) (secondMoment n r) r)
    (hZ0 : partition n r ≠ 0) :
    deriv (orientationMean n) r =
      secondMoment n r / partition n r - (orientationMean n r) ^ 2 := by
  have hquot := hM.div hZ hZ0
  have hder : deriv (orientationMean n) r =
      (secondMoment n r * partition n r -
        firstMoment n r * firstMoment n r) / (partition n r) ^ 2 := by
    exact hquot.deriv
  rw [hder]
  unfold orientationMean
  field_simp [hZ0]

end DFL
