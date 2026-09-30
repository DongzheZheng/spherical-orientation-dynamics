import DFL.Hysteresis.OriginalTrajectory

/-!
# The target bridge from the original elasticity signs to a single valley

This final calculus bridge uses the actual DFL equilibrium density and the
exact slope identity.  Its hypotheses are the sign pattern of the *actual*
elasticity difference `OriginalTrajectory.H`; they are not asserted here.
-/

namespace DFL.Hysteresis

open Set

private theorem original_density_deriv_neg (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r)
    (hH : OriginalTrajectory.H n r < 0) :
    deriv (DFL.equilibriumDensity n) r < 0 := by
  have hR : 0 < DFL.equilibriumDensity n r := equilibriumDensity_pos n hn hr
  have hslope := OriginalTrajectory.original_density_slope n hn hr
  have hprod : DFL.equilibriumDensity n r * OriginalTrajectory.H n r < 0 :=
    mul_neg_of_pos_of_neg hR hH
  have hder : deriv (DFL.equilibriumDensity n) r =
      (DFL.equilibriumDensity n r * OriginalTrajectory.H n r) / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    simpa only [mul_comm] using hslope
  rw [hder]
  exact div_neg_of_neg_of_pos hprod hr

private theorem original_density_deriv_pos (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r)
    (hH : 0 < OriginalTrajectory.H n r) :
    0 < deriv (DFL.equilibriumDensity n) r := by
  have hR : 0 < DFL.equilibriumDensity n r := equilibriumDensity_pos n hn hr
  have hslope := OriginalTrajectory.original_density_slope n hn hr
  have hprod : 0 < DFL.equilibriumDensity n r * OriginalTrajectory.H n r :=
    mul_pos hR hH
  have hder : deriv (DFL.equilibriumDensity n) r =
      (DFL.equilibriumDensity n r * OriginalTrajectory.H n r) / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    simpa only [mul_comm] using hslope
  rw [hder]
  exact div_pos hprod hr

/-- If the actual DFL elasticity difference has a unique strict crossing,
the historical positive-axis single-valley target follows exactly. -/
theorem isUnimodal_of_original_H_signs (n : ℕ) (hn : 2 ≤ n)
    {rStar : ℝ} (hrStar : 0 < rStar)
    (hzero : OriginalTrajectory.H n rStar = 0)
    (hneg : ∀ r : ℝ, 0 < r → r < rStar → OriginalTrajectory.H n r < 0)
    (hpos : ∀ r : ℝ, rStar < r → 0 < OriginalTrajectory.H n r) :
    DFL.IsUnimodal n := by
  let R := DFL.equilibriumDensity n
  have hderneg : ∀ r : ℝ, 0 < r → r < rStar → deriv R r < 0 := by
    intro r hr hrlt
    exact original_density_deriv_neg n hn hr (hneg r hr hrlt)
  have hderpos : ∀ r : ℝ, rStar < r → 0 < deriv R r := by
    intro r hrlt
    exact original_density_deriv_pos n hn (lt_trans hrStar hrlt) (hpos r hrlt)
  have hanti : StrictAntiOn R (Ioc 0 rStar) := by
    have hcont : ContinuousOn R (Ioc 0 rStar) := by
      intro r hr
      exact (DFL.equilibriumDensity_differentiableAt n hn hr.1).continuousAt.continuousWithinAt
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 rStar) hcont
    intro r hr
    have hr' : r ∈ Ioo 0 rStar := by simpa using hr
    exact hderneg r hr'.1 hr'.2
  have hmono : StrictMonoOn R (Ici rStar) := by
    have hcont : ContinuousOn R (Ici rStar) := by
      intro r hr
      exact (DFL.equilibriumDensity_differentiableAt n hn
        (lt_of_lt_of_le hrStar hr)).continuousAt.continuousWithinAt
    apply strictMonoOn_of_deriv_pos (convex_Ici rStar) hcont
    intro r hr
    have hr' : r ∈ Ioi rStar := by simpa using hr
    exact hderpos r hr'
  have hderzero : deriv R rStar = 0 := by
    have hslope := OriginalTrajectory.original_density_slope n hn hrStar
    rw [hzero, mul_zero] at hslope
    exact (mul_eq_zero.mp hslope).resolve_left (ne_of_gt hrStar)
  have hunique : ∀ r : ℝ, 0 < r → deriv R r = 0 → r = rStar := by
    intro r hr hz
    rcases lt_trichotomy r rStar with hlt | heq | hgt
    · have h := hderneg r hr hlt
      rw [hz] at h
      exact False.elim (lt_irrefl 0 h)
    · exact heq
    · have h := hderpos r hgt
      rw [hz] at h
      exact False.elim (lt_irrefl 0 h)
  exact ⟨rStar, hrStar, hanti, hmono, hderzero, hunique⟩

end DFL.Hysteresis
