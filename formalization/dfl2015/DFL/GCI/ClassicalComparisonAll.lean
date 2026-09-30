import DFL.GCI.ComparisonAll
import DFL.GCI.ClassicalEnergyDomainBridge

/-! The full original GCI comparison with its classical domain certified.
The Dirichlet graph is the closure of actual compactly supported smooth
functions and their derivatives; the density and domain equivalence are
proved, and the original singular potential condition is retained. -/

namespace DFL.GCI
noncomputable section

theorem original_GCI_all_classicalH10_strict_shift_chain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState,
      OriginalWeakGCISolution n r s ∧
      ClassicalDirichletRepresentative n s ∧
      MeasureTheory.MemLp (angularPotentialRepresentative n s) 2 angularLebesgue ∧
      (∀ v : AngularState, OriginalWeakGCISolution n r v →
        originalGCICoefficient n r v = originalGCICoefficient n r s) ∧
      0 < originalGCIDenominator n r s ∧
      0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s < DFL.orientationMean (n+2) r ∧
      DFL.orientationMean (n+2) r < DFL.orientationMean n r := by
  obtain ⟨s, hs, huniq, hD, hpos, hshift, hupper⟩ :=
    original_GCI_all_strict_shift_chain n hn r hr
  obtain ⟨hrep, hpot⟩ := (angularEnergyDomain_iff_classicalH10_potential n s).mp hs.1
  exact ⟨s, hs, hrep, hpot, huniq, hD, hpos, hshift, hupper⟩

end
end DFL.GCI
