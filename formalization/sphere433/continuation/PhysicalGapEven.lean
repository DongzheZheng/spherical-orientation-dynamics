import continuation.PhysicalGapEigenComparison

/-! Original antipodal reflection proof for the complete physical gap.
The actual first state is reflected through the genuine sphere isometry,
then compared to the other actual full-domain minimum. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLGroundSymmetry DFLPhysicalHalfDensity
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]

private theorem actual_weighted_gap_reflected_le (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedGap (n := n) p (-r)≤weightedGap (n := n) p r := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨hl,f,_hM,_hm,_hE,heig,⟨x,hx⟩,_hmin⟩ := actual_weighted_gap_spec (n := n) p hp r
  have hfne : (f : sphere (0 : E) 1 → ℝ) ≠ 0 := by
    intro h; exact hx (congrFun h x)
  obtain ⟨S,_hS,hSn,hSe,_hSo,_hSE,_hSw⟩ := smooth_weighted_eigen_half_density
    (n := n) p hp r _ hl.ne' f hfne heig
  let Φ := sphereDiffeo (n := n) (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)
  let T : SmoothScalar g := ⟨fun y => S.toFun (Φ y),S.smooth.comp Φ.contMDiff⟩
  have hV (y : sphere (0 : E) 1) : driftPotential n p r (Φ y)=driftPotential n p (-r) y := by
    unfold driftPotential
    change r^2/4*(1-⟪p,(Φ y : E)⟫_ℝ^2)-r*(n : ℝ)/2*⟪p,(Φ y : E)⟫_ℝ = _
    rw [sphereDiffeo_coe]
    simp only [LinearIsometryEquiv.coe_neg,inner_neg_right]
    ring
  have hT : ∀ y,-ΔG g T.toContMDiffMap y+driftPotential n p (-r) y*T.toFun y=
      weightedGap (n := n) p r*T.toFun y := by
    intro y
    have hm : T.toContMDiffMap=orthogonalPullback (LinearIsometryEquiv.neg ℝ) S.toContMDiffMap := by
      ext z; rfl
    rw [hm,orthogonalPullback_laplacian]
    change -ΔG g S.toContMDiffMap (Φ y)+driftPotential n p (-r) y*S.toFun (Φ y)=_
    rw [← hV y]
    exact hSe (Φ y)
  let u := inverseHalfDensity (n := n) p (-r) T.toContMDiffMap
  have hu : ∀ y,weightedRoundApply (n := n) p (-r) u y=weightedGap (n := n) p r*u y := by
    apply schrodinger_to_weighted_eigenfunction p hp (-r) _ T.toContMDiffMap
    intro y
    rw [physicalPotential_eq_drift]
    exact hT y
  have hun : (u : sphere (0 : E) 1 → ℝ) ≠ 0 := by
    intro hz
    have hs0 : S=0 := by
      ext y
      have hh := congrFun hz (Φ.symm y)
      change halfFactor p (-(-r)) (Φ.symm y)*S.toFun (Φ (Φ.symm y))=0 at hh
      rw [neg_neg,Φ.apply_symm_apply] at hh
      exact (mul_eq_zero.mp hh).resolve_left (Real.exp_pos _).ne'
    rw [hs0,(smoothToLp g).map_zero,norm_zero] at hSn
    exact (lt_irrefl 0) hSn
  exact actual_weighted_gap_le_positive_eigenvalue (n := n) p hp (-r) _ hl u hun hu

/-- Reversing the field preserves the actual complete physical gap,
for every real field and every sphere dimension n≥1. -/
theorem actual_weighted_gap_even (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedGap (n := n) p (-r)=weightedGap (n := n) p r := by
  exact le_antisymm (actual_weighted_gap_reflected_le p hp r)
    (by simpa only [neg_neg] using actual_weighted_gap_reflected_le (n := n) p hp (-r))
end DFLPhysicalGap
