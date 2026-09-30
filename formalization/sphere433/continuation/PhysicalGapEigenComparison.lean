import continuation.PhysicalGapFullDomain
import continuation.TransverseFirstMinimumUpper

/-! Every genuine nonzero positive weighted eigenfunction is a trial state
for the same original full-domain gap, by its actual half-density state. -/
noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]

/-- The actual full-domain physical gap lies below every nonzero smooth
positive weighted eigenvalue. Equilibrium orthogonality and trial energy
are proved from the true equations. -/
theorem actual_weighted_gap_le_positive_eigenvalue (p : E) (hp : ‖p‖=1)
    (r lam : ℝ) (hlam : 0<lam) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hfne : (f : sphere (0 : E) 1 → ℝ) ≠ 0)
    (heig : ∀ x,weightedRoundApply (n := n) p r f x=lam*f x) :
    weightedGap (n := n) p r≤lam := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨S,_hS,hSn,_hSe,hSo,hSE,_hSw⟩ := smooth_weighted_eigen_half_density
    (n := n) p hp r lam hlam.ne' f hfne heig
  obtain ⟨e,_U,_hen,_hep,⟨c,_hc,hce⟩,_hUn,_hUo,_hUE,_hUw,hmin⟩ :=
    actual_weighted_gap_full_H1_minimum (n := n) p hp r
  have horth : ⟪H1ComplToLp g (smoothToH1Compl g S),smoothToLp g e⟫_ℝ=0 := by
    rw [H1ComplToLp_smoothToH1Compl,hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),real_inner_smul_right,hSo,mul_zero]
  have hh := hmin (smoothToH1Compl g S) horth
  rw [H1ComplToLp_smoothToH1Compl,hSE] at hh
  exact le_of_mul_le_mul_right hh (sq_pos_of_pos hSn)
end DFLPhysicalGap
