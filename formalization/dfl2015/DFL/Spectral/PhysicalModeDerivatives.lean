import DFL.Spectral.GroundHF

/-!
# Exact physical dimension substitutions in the manuscript's derivative proof

These are applications of the already proved ODE/Green/flux argument, at
the source's angular and radial parameters. The eigenstate construction
and full-sphere first-mode identification remain explicit missing bridges.
-/

namespace DFL.Spectral

open Set

noncomputable section

theorem positive_latitude_eigenfunction_strictAnti
    (M : ℕ) (hM : 0 < M) (b lam0 r lam : ℝ) (hbr : 0 < b * r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r lam v) :
    StrictAntiOn v (Icc (-1 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hv.continuous.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  exact positive_latitude_eigenfunction_deriv_neg M hM b lam0 r lam hbr v hv hpos heq ht

/-- Every physical angular mode has `M=d+2ℓ`, `b=ℓ`, and the strict
positive parameter derivative follows from its source-aligned eigenpair
and parameter derivative equation. This does not construct that pair. -/
theorem physical_angular_eigenpair_derivative_pos
    (d ell : ℕ) (hd : 1 ≤ d) (hell : 1 ≤ ell) (r lam lamPrime : ℝ) (hr : 0 < r)
    (v g : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation (d + 2 * ell) (ell : ℝ)
      ((ell : ℝ) * ((ell : ℝ) + (d : ℝ) - 1)) r lam v)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply (d + 2 * ell) (ell : ℝ)
        ((ell : ℝ) * ((ell : ℝ) + (d : ℝ) - 1)) r g t +
      halfDensityPotentialPrime (d + 2 * ell) (ell : ℝ) r t * halfDensityLift r v t =
        lamPrime * halfDensityLift r v t + lam * g t) :
    0 < lamPrime := by
  apply latitude_eigenpair_parameter_derivative_pos
    (d + 2 * ell) (by omega) (ell : ℝ)
    ((ell : ℝ) * ((ell : ℝ) + (d : ℝ) - 1)) r lam lamPrime
    (by exact_mod_cast (show 0 < ell by omega)) _ hr v g hv hg hpos heq hparameter
  push_cast
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  linarith

/-- The radial derivative partner has `M=d+2`, `b=2`, `lam0=d`.
Its parameter derivative is strictly positive for the source range `d≥2`. -/
theorem physical_radial_partner_eigenpair_derivative_pos
    (d : ℕ) (hd : 2 ≤ d) (r lam lamPrime : ℝ) (hr : 0 < r)
    (v g : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation (d + 2) 2 (d : ℝ) r lam v)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply (d + 2) 2 (d : ℝ) r g t +
        halfDensityPotentialPrime (d + 2) 2 r t * halfDensityLift r v t =
      lamPrime * halfDensityLift r v t + lam * g t) :
    0 < lamPrime := by
  apply latitude_eigenpair_parameter_derivative_pos (d + 2) (by omega)
    2 (d : ℝ) r lam lamPrime (by norm_num) _ hr v g hv hg hpos heq hparameter
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  push_cast
  linarith

/-- The same theorem applies to an actual differentiable eigenvalue
curve, once its derivative eigen-equation is supplied by that curve. -/
theorem latitude_branch_deriv_pos
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lamPrime : ℝ)
    (hb : 0 < b) (hbhalf : 2 * b ≤ (M : ℝ)) (hr : 0 < r)
    (Lambda : ℝ → ℝ) (hLambda : HasDerivAt Lambda lamPrime r)
    (v g : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r (Lambda r) v)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply M b lam0 r g t + halfDensityPotentialPrime M b r t *
        halfDensityLift r v t = lamPrime * halfDensityLift r v t + Lambda r * g t) :
    0 < deriv Lambda r := by
  rw [hLambda.deriv]
  exact latitude_eigenpair_parameter_derivative_pos M hM b lam0 r (Lambda r) lamPrime
    hb hbhalf hr v g hv hg hpos heq hparameter

end

end DFL.Spectral
