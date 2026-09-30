import DFL.Hysteresis.MomentRecurrence
import DFL.Hysteresis.MarginalDerivative
import DFL.Hysteresis.ElasticityODE

/-!
# Riccati and elasticity ODE for the original spherical mean

These theorems apply the recurrence proved from the exact marginal in
`DFL.Targets` and the separately proved parameter derivatives of its moments.
No Riccati or elasticity equation is introduced as an assumption here.
-/

namespace DFL

/-- The Riccati identity of `hyst:riccati` for the original normalized
spherical mean, in every embedding dimension `n ≥ 2` and at every `r > 0`. -/
theorem orientationMean_riccati (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    Hysteresis.ElasticityODE.RiccatiAt n (orientationMean n) r := by
  change deriv (orientationMean n) r =
    1 - ((n : ℝ) - 1) * orientationMean n r / r -
      (orientationMean n r) ^ 2
  exact orientationMean_riccati_of_moment_derivs n hn hr
    (partition_hasDerivAt_firstMoment n hn r)
    (firstMoment_hasDerivAt_secondMoment n hn r)

/-- The elasticity ODE of `hyst:elasticity-ode` for the same original
von Mises--Fisher marginal.  The generic calculus theorem receives only
properties already proved for that marginal. -/
theorem orientationMean_elasticity_ode (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    r * deriv (Hysteresis.ElasticityODE.elasticity (orientationMean n)) r =
      ((n : ℝ) - 1 +
          Hysteresis.ElasticityODE.elasticity (orientationMean n) r) *
        (1 - Hysteresis.ElasticityODE.elasticity (orientationMean n) r) -
      2 * Hysteresis.ElasticityODE.elasticity (orientationMean n) r *
        Hysteresis.ElasticityODE.scaledMean (orientationMean n) r := by
  apply Hysteresis.ElasticityODE.elasticity_ode n (orientationMean n) hr
  intro x hx
  exact ⟨orientationMean_pos n hn hx,
    orientationMean_differentiableAt n hn x,
    orientationMean_riccati n hn hx⟩

end DFL
