import DFL.GCI.GraphPhysicalForm
import DFL.GCI.GraphDomainBridge
import DFL.GCI.ExplicitSolution2D

/-! Lax--Milgram existence transported to the original angular weak
equation. Every test is from the original represented source domain;
the closed graph is only its Hilbert-space realization. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem graph_originalWeakForm (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (p : dirichletGraph) (v : AngularState) (hv : AngularEnergyDomain n v) :
    graphEnergyBilinear n r p (stateToGraph n hn v hv) =
      originalWeakForm n r (graphState n p) v := by
  rw [graphEnergyBilinear_integral n hn]
  unfold originalWeakForm
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  change (∫ θ, graphPhysicalFormDensity n r p (stateToGraph n hn v hv) θ ∂angularLebesgue) =
    ∫ θ, formIntegrand n r (graphState n p) v θ ∂angularLebesgue
  apply integral_congr_ae
  filter_upwards [graph_ae_interior, graphState_singular_ae n p,
    stateToGraph_derivative_ae n hn v hv,
    stateToGraph_singular_ae n hn v hv] with θ hθ hp hq hy
  rw [formIntegrand_scaled_density n (graphState n p) v
    (graphState_mem_energy n hn p) hv r θ hθ]
  unfold graphPhysicalFormDensity
  rw [hq, hy, hp]
  rfl

theorem graph_originalSourcePairing (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (v : AngularState) (hv : AngularEnergyDomain n v) :
    graphPhysicalSource n hn r (stateToGraph n hn v hv) =
      originalSourcePairing n r v := by
  rw [graphPhysicalSource_integral,
    originalSourcePairing_eq_denominator n (by omega)]
  unfold originalGCIDenominator
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  change (∫ θ, graphSourceDensity n r θ *
      (graphSingular (stateToGraph n hn v hv)) θ ∂angularLebesgue) =
    ∫ θ, v.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1) ∂angularLebesgue
  apply integral_congr_ae
  filter_upwards [graph_ae_interior, stateToGraph_singular_ae n hn v hv]
    with θ hθ hy
  rw [denominator_density_eq_scaled n v hv r θ hθ, hy]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hpow : Real.rpow (Real.sin θ) (halfPower n + 2) =
      Real.rpow (Real.sin θ) (halfPower n + 1) * Real.sin θ := by
    have he : halfPower n + 2 = (halfPower n + 1) + 1 := by ring
    rw [he]
    exact Real.rpow_add_one hsin.ne' _
  unfold graphSourceDensity momentDenominatorWeight singularRepresentative
  rw [hpow]
  field_simp [hsin.ne']

/-- An actual represented original angular weak solution exists in every
ambient dimension `n≥3`, for every field. No solution, sign, or coefficient
comparison is assumed. -/
theorem original_weak_solution_exists_ge_three (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    ∃ s : AngularState, OriginalWeakGCISolution n r s := by
  obtain ⟨p, hp, _⟩ := graph_original_source_exists_unique n hn r
  refine ⟨graphState n p, graphState_mem_energy n hn p, ?_⟩
  intro v hv
  refine ⟨formIntegrand_intervalIntegrable_of_energyDomain n (by omega) r
    (graphState n p) v (graphState_mem_energy n hn p) hv,
    source_intervalIntegrable_of_energyDomain n (by omega) r v hv, ?_⟩
  rw [← graph_originalWeakForm n hn r p v hv,
    ← graph_originalSourcePairing n hn r v hv]
  exact hp (stateToGraph n hn v hv)

/-- The actual represented original GCI weak problem has a solution in
every historical ambient dimension at every positive concentration. -/
theorem original_weak_GCI_exists_all (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ s : AngularState, OriginalWeakGCISolution n r s := by
  by_cases htwo : n = 2
  · subst n
    exact ⟨explicitState r, explicit_original_weak_solution_twoD r hr⟩
  · exact original_weak_solution_exists_ge_three n (by omega) r

end
end DFL.GCI
