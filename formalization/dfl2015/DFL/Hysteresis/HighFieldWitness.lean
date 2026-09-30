import DFL.Hysteresis.MeanEndpoints
import DFL.Hysteresis.OriginalTrajectory

/-!
# A positive high-field elasticity witness on the original branch

The single-valley crossing argument only needs `H > 0` at some field beyond
each prescribed lower bound.  This follows from the original density branch
being unbounded and differentiable, together with its exact slope identity.
It does not require the stronger asymptotic claim `r c'(r)/c(r) → 0`.
-/

namespace DFL.Hysteresis

open Set Filter
open scoped Topology

/-- For every positive field threshold there is a later field where the
actual DFL elasticity difference is positive.  The proof uses the original
spherical marginal and physical feedback branch throughout. -/
theorem original_H_positive_arbitrarily_late (n : ℕ) (hn : 2 ≤ n)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r : ℝ, r₀ < r ∧ 0 < OriginalTrajectory.H n r := by
  let R := DFL.equilibriumDensity n
  have hlarge : ∀ᶠ L : ℝ in atTop, R r₀ < R L :=
    (DFL.equilibriumDensity_tendsto_atTop n hn).eventually_gt_atTop (R r₀)
  obtain ⟨L, hRL, hrL⟩ :=
    (hlarge.and (eventually_gt_atTop r₀)).exists
  have hcont : ContinuousOn R (Icc r₀ L) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hx.1
    exact (DFL.equilibriumDensity_differentiableAt n hn hxpos).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ R (Ioo r₀ L) := by
    intro x hx
    have hxpos : 0 < x := lt_trans hr₀ hx.1
    exact (DFL.equilibriumDensity_differentiableAt n hn hxpos).differentiableWithinAt
  obtain ⟨r, hr, hder⟩ :=
    exists_deriv_eq_slope R hrL hcont hdiff
  have hrpos : 0 < r := lt_trans hr₀ hr.1
  have hderpos : 0 < deriv R r := by
    rw [hder]
    exact div_pos (sub_pos.mpr hRL) (sub_pos.mpr hrL)
  have hRpos : 0 < R r := equilibriumDensity_pos n hn hrpos
  have hslope := OriginalTrajectory.original_density_slope n hn hrpos
  have hprod : 0 < R r * OriginalTrajectory.H n r := by
    rw [← hslope]
    exact mul_pos hrpos hderpos
  have hHpos : 0 < OriginalTrajectory.H n r := by
    by_contra h
    have hnonpos : OriginalTrajectory.H n r ≤ 0 := le_of_not_gt h
    have := mul_nonpos_of_nonneg_of_nonpos hRpos.le hnonpos
    exact (not_le_of_gt hprod) this
  exact ⟨r, hr.1, hHpos⟩

end DFL.Hysteresis
