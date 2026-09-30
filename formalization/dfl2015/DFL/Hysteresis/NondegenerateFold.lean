import DFL.Hysteresis.SmallFieldSign
import DFL.Hysteresis.OriginalCrossing

/-!
# Nondegenerate fold of the original DFL density curve

The second derivative is computed from the exact slope identity on a positive
neighborhood of the unique elasticity crossing.  No second-order expansion
of the spherical integral is assumed.
-/

namespace DFL.Hysteresis

open Set Filter
open scoped Topology
open DFL.Hysteresis.OriginalTrajectory

noncomputable section

/-- Pointwise slope of the original equilibrium density, with a positive
coefficient multiplying the actual elasticity difference. -/
theorem original_density_deriv_eq_coeff_mul_H (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    deriv (DFL.equilibriumDensity n) r =
      (DFL.equilibriumDensity n r / r) * H n r := by
  have hslope := original_density_slope n hn hr
  have hder : deriv (DFL.equilibriumDensity n) r =
      (DFL.equilibriumDensity n r * H n r) / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    simpa only [mul_comm] using hslope
  calc
    deriv (DFL.equilibriumDensity n) r =
        (DFL.equilibriumDensity n r * H n r) / r := hder
    _ = (DFL.equilibriumDensity n r / r) * H n r := by ring

/-- The second derivative at any positive zero with strictly positive `H'`.
The differentiability of `H` follows from its nonzero derivative; the
identity for `R'` holds throughout a positive neighborhood. -/
theorem original_density_second_deriv_at_H_zero (n : ℕ) (hn : 2 ≤ n)
    {rstar : ℝ} (hrstar : 0 < rstar)
    (hzero : H n rstar = 0)
    (hHder : 0 < deriv (H n) rstar) :
    deriv (deriv (DFL.equilibriumDensity n)) rstar =
      (DFL.equilibriumDensity n rstar / rstar) * deriv (H n) rstar := by
  let R := DFL.equilibriumDensity n
  have hlocal : deriv R =ᶠ[𝓝 rstar]
      (fun x : ℝ => (R x / x) * H n x) := by
    filter_upwards [Ioi_mem_nhds hrstar] with x hx
    exact original_density_deriv_eq_coeff_mul_H n hn hx
  have hR : DifferentiableAt ℝ R rstar :=
    DFL.equilibriumDensity_differentiableAt n hn hrstar
  have hdiv : DifferentiableAt ℝ (fun x : ℝ => R x / x) rstar :=
    hR.div differentiableAt_id (ne_of_gt hrstar)
  have hH : DifferentiableAt ℝ (H n) rstar :=
    differentiableAt_of_deriv_ne_zero (ne_of_gt hHder)
  rw [hlocal.deriv_eq]
  change deriv ((fun x : ℝ => R x / x) * H n) rstar =
    (DFL.equilibriumDensity n rstar / rstar) * deriv (H n) rstar
  rw [deriv_mul hdiv hH, hzero]
  ring

/-- Formula-level nondegenerate fold for every sphere dimension `n ≥ 2`.
The small-field negative sign, unique crossing and high-field positive witness
are all theorems about the same original spherical marginal. -/
theorem original_nondegenerateFold (n : ℕ) (hn : 2 ≤ n) :
    DFL.NondegenerateFold n := by
  have hsmall : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r ≤ δ → H n r < 0 := by
    refine ⟨(1 / 8 : ℝ), by norm_num, ?_⟩
    intro r hr hrδ
    exact SmallFieldSign.original_H_neg_small n hn hr
      (lt_of_le_of_lt hrδ (by norm_num))
  obtain ⟨rstar, hrstar, hzero, hneg, hpos, hHder, _⟩ :=
    OriginalCrossing.crossing_of_small_negative n hn hsmall
  refine ⟨rstar, hrstar, ?_, ?_, ?_, ?_⟩
  · intro r hr hrlt
    rw [original_density_deriv_eq_coeff_mul_H n hn hr]
    exact mul_neg_of_pos_of_neg
      (div_pos (equilibriumDensity_pos n hn hr) hr)
      (hneg r hr hrlt)
  · rw [original_density_deriv_eq_coeff_mul_H n hn hrstar, hzero]
    ring
  · intro r hrlt
    have hr : 0 < r := lt_trans hrstar hrlt
    rw [original_density_deriv_eq_coeff_mul_H n hn hr]
    exact mul_pos (div_pos (equilibriumDensity_pos n hn hr) hr)
      (hpos r hrlt)
  · rw [original_density_second_deriv_at_H_zero n hn hrstar hzero hHder]
    exact mul_pos
      (div_pos (equilibriumDensity_pos n hn hrstar) hrstar) hHder

end

end DFL.Hysteresis
