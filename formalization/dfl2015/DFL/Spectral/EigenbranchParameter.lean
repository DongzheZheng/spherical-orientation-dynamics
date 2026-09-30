import DFL.Spectral.GroundHF

/-!
# Differentiating the actual eigenbranch equation

The parameter equation used in the Green/HF argument is derived here
from the eigen-equation along a genuine scalar eigenvalue function.
The three parameter derivative identities express differentiability of
the eigenfunction and its first two latitude derivatives in a fixed domain.
Existence of such a branch remains a separate spectral-theory obligation.
-/

namespace DFL.Spectral

open Set

noncomputable section

theorem halfDensityPotential_parameter_deriv
    (M : ℕ) (b lam0 r t : ℝ) :
    HasDerivAt (fun ρ => halfDensityPotential M b lam0 ρ t)
      (halfDensityPotentialPrime M b r t) r := by
  convert ((hasDerivAt_const r lam0).add
    (((hasDerivAt_id r).pow 2).div_const 4 |>.mul_const (1 - t ^ 2))).add
    (((hasDerivAt_id r).const_mul (b - (M : ℝ) / 2)).mul_const t) using 1
  all_goals
    simp only [halfDensityPotential, halfDensityPotentialPrime, Pi.pow_apply, id_eq]
    try funext ρ
    dsimp
    norm_num
    try ring_nf
    try simp

/-- Formal derivative of the original fixed-domain eigen-equation,
without assuming the differentiated equation or a HF formula. -/
theorem halfDensity_parameter_equation_of_eigenbranch
    (M : ℕ) (b lam0 r lamPrime t : ℝ)
    (lam : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hlam : HasDerivAt lam lamPrime r)
    (hu : HasDerivAt (fun ρ => u ρ t) (g t) r)
    (hut : HasDerivAt (fun ρ => deriv (u ρ) t) (deriv g t) r)
    (hutt : HasDerivAt (fun ρ => deriv (deriv (u ρ)) t)
      (deriv (deriv g) t) r)
    (heq : ∀ ρ, halfDensityApply M b lam0 ρ (u ρ) t = lam ρ * u ρ t) :
    halfDensityApply M b lam0 r g t +
        halfDensityPotentialPrime M b r t * u r t =
      lamPrime * u r t + lam r * g t := by
  have hleft : HasDerivAt (fun ρ => halfDensityApply M b lam0 ρ (u ρ) t)
      (halfDensityApply M b lam0 r g t +
        halfDensityPotentialPrime M b r t * u r t) r := by
    convert ((hutt.const_mul (-(1 - t ^ 2))).add
      (hut.const_mul ((M : ℝ) * t))).add
      ((halfDensityPotential_parameter_deriv M b lam0 r t).mul hu) using 1
    all_goals
      simp only [halfDensityApply]
      ring
  have hright := hlam.mul hu
  have heqfun : (fun ρ => halfDensityApply M b lam0 ρ (u ρ) t) =
      (fun ρ => lam ρ * u ρ t) := funext heq
  rw [heqfun] at hleft
  exact hleft.unique hright

/-- A concrete differentiable eigenvalue branch has positive derivative
when its positive latitude eigenfunction and fixed-domain mixed derivative
identities satisfy the original conditions. -/
theorem actual_eigenbranch_derivative_pos
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r : ℝ)
    (hb : 0 < b) (hbhalf : 2 * b ≤ (M : ℝ)) (hr : 0 < r)
    (lam : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (v g : ℝ → ℝ)
    (hlam : DifferentiableAt ℝ lam r)
    (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heqv : LatitudeEigenEquation M b lam0 r (lam r) v)
    (hslice : u r = halfDensityLift r v)
    (hu : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun ρ => u ρ t) (g t) r)
    (hut : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun ρ => deriv (u ρ) t) (deriv g t) r)
    (hutt : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun ρ => deriv (deriv (u ρ)) t) (deriv (deriv g) t) r)
    (heq : ∀ ρ t, t ∈ Ioo (-1 : ℝ) 1 →
      halfDensityApply M b lam0 ρ (u ρ) t = lam ρ * u ρ t) :
    0 < deriv lam r := by
  apply latitude_eigenpair_parameter_derivative_pos M hM b lam0 r (lam r)
    (deriv lam r) hb hbhalf hr v g hv hg hpos heqv
  intro t ht
  have h := halfDensity_parameter_equation_of_eigenbranch M b lam0 r
    (deriv lam r) t lam u g hlam.hasDerivAt (hu t ht) (hut t ht)
    (hutt t ht) (fun ρ => heq ρ t ht)
  simpa only [hslice] using h

end
end DFL.Spectral
