import DFL.GCI.AngularMassCauchy3D

/-!
# Exact remaining spectral bridge for the original dimension-three GCI numerator

This lemma isolates a sufficient *original quadratic-form* assertion.
The spectral premise is not asserted here: it must be proved on the
represented source domain from the positive angular supersolution with
the singular endpoint terms controlled.
-/

namespace DFL.GCI

noncomputable section

/-- The strict original first-mode spectral inequality on the actual
weak solution implies the positive original hydrodynamic numerator.
No sign, monotonicity, or coefficient bound is assumed. -/
theorem weak_solution_numerator_pos_three_of_spectral_gap
    (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution 3 r s)
    (hgap : 2 * threeDWeightedMass r s <
      originalWeakForm 3 r s s) :
    0 < originalGCINumerator 3 r s := by
  have hDpos := weak_solution_denominator_pos 3 (by omega) r s hs
  have hZpos := originalForcingNorm_pos_of_weak_solution
    3 (by omega) r s hs
  have hEnergy : originalWeakForm 3 r s s =
      originalGCIDenominator 3 r s := by
    calc
      _ = originalSourcePairing 3 r s := (hs.2 s hs.1).2.2
      _ = originalGCIDenominator 3 r s :=
        originalSourcePairing_eq_denominator 3 (by omega) r s
  have hgap' : 2 * threeDWeightedMass r s <
      originalGCIDenominator 3 r s := by
    rw [hEnergy] at hgap
    exact hgap
  have hCauchy := weak_solution_weighted_mass_cauchy_threeD r s hs
  have hZgreater : 2 * originalGCIDenominator 3 r s <
      originalForcingNorm 3 r := by
    by_contra h
    have hle : originalForcingNorm 3 r ≤
        2 * originalGCIDenominator 3 r s := le_of_not_gt h
    have hprod := mul_le_mul_of_nonneg_right hle hDpos.le
    have hspec := mul_lt_mul_of_pos_left hgap' hZpos
    nlinarith [hprod, hspec, hCauchy]
  have hMoment := weak_solution_moment_identity_three r s hs
  have hRN : 0 < r * originalGCINumerator 3 r s := by
    linarith [hMoment]
  exact (mul_pos_iff_of_pos_left hr).mp hRN

end

end DFL.GCI
