import Mathlib

/-!
# DFL historical conjecture targets

This file states a target; it does not claim a proof.  The integral is the
one-dimensional formula for the first-coordinate marginal of normalized
von Mises--Fisher surface measure on `S^(n-1)`.  The geometric pushforward
identity is proved in Lean for every physical sphere `n ≥ 2` in the
separate `Geometry/PhysicalSphereAll.lean` import chain. Its
dimension-dependent normalizing constant cancels in `orientationMean`.
In particular, `n = 2` has exponent `-1/2`, so endpoint integrability must
be proved and is included as a separate support target rather than assumed.

Source: Degond--Frouvelle--Liu, *Phase Transitions, Hysteresis, and
Hyperbolicity for Self-Organized Alignment Dynamics*, ARMA 216 (2015),
Section 4.3, immediately before Proposition 4.3.
-/

namespace DFL

open MeasureTheory
open Filter
open scoped Interval

noncomputable section

/-- Unnormalized first-coordinate marginal of the von Mises--Fisher law on
`S^(n-1)`.  The harmless values assigned at `t = ±1` do not change the integral. -/
def marginalWeight (n : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (r * t) * Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2)

/-- Unnormalized partition function for the spherical first-coordinate law. -/
def partition (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, marginalWeight n r t

/-- Unnormalized first moment for the same law. -/
def firstMoment (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, t * marginalWeight n r t

/-- `c_{n-1}(r)` in the manuscript: the actual spherical orientation mean.
The geometric surface-area constant cancels between numerator and denominator. -/
def orientationMean (n : ℕ) (r : ℝ) : ℝ :=
  firstMoment n r / partition n r

/-- `j(r) = k⁻¹(r)` for the original feedback `k(J) = J + J²`, `J ≥ 0`. -/
def inverseAlignment (r : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * r) - 1) / 2

/-- Original equilibrium density curve `j(r) / c_{n-1}(r)`, for `r > 0`. -/
def equilibriumDensity (n : ℕ) (r : ℝ) : ℝ :=
  inverseAlignment r / orientationMean n r

/-- Analytic support target for the original marginal.  This is kept
separate from the historical conjecture itself, and is not an assumption
silently available to a future proof. -/
def MarginalWellDefined (n : ℕ) : Prop :=
  ∀ r : ℝ, 0 < r →
    IntervalIntegrable (marginalWeight n r) volume (-1 : ℝ) 1 ∧
    IntervalIntegrable (fun t : ℝ => t * marginalWeight n r t) volume (-1 : ℝ) 1 ∧
    0 < partition n r ∧ 0 < orientationMean n r ∧
    DifferentiableAt ℝ (equilibriumDensity n) r

/-- The value `R_n(0) = n` in the original paper is a continuous extension,
since the raw quotient at `r = 0` is `0 / 0`. -/
def EndpointAtZero (n : ℕ) : Prop :=
  Tendsto (equilibriumDensity n)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (n : ℝ))

/-- The historical single-valley statement on the positive concentration
axis: a unique critical point, strict decrease up to it and strict increase
after it.  Monotonicity is stated as such, without replacing it by the
stronger assertion that the derivative has a strict sign everywhere. -/
def IsUnimodal (n : ℕ) : Prop :=
  ∃ rStar : ℝ,
    0 < rStar ∧
    StrictAntiOn (equilibriumDensity n) (Set.Ioc 0 rStar) ∧
    StrictMonoOn (equilibriumDensity n) (Set.Ici rStar) ∧
    deriv (equilibriumDensity n) rStar = 0 ∧
    (∀ r : ℝ, 0 < r → deriv (equilibriumDensity n) r = 0 → r = rStar)

/-- Root target for the DFL 2015 Section 4.3 unimodality conjecture.
No theorem of this type is asserted in this file. -/
def DFL2015UnimodalityConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → IsUnimodal n

/-- The manuscript's pointwise derivative signs and nondegenerate fold are
strictly stronger than the historical monotonicity statement.  Keep them as
a separate target, never as a reformulation of the historical conjecture. -/
def NondegenerateFold (n : ℕ) : Prop :=
  ∃ rStar : ℝ,
    0 < rStar ∧
    (∀ r : ℝ, 0 < r → r < rStar → deriv (equilibriumDensity n) r < 0) ∧
    deriv (equilibriumDensity n) rStar = 0 ∧
    (∀ r : ℝ, rStar < r → 0 < deriv (equilibriumDensity n) r) ∧
    0 < deriv (deriv (equilibriumDensity n)) rStar

#check DFL2015UnimodalityConjecture
#check NondegenerateFold

end

end DFL
