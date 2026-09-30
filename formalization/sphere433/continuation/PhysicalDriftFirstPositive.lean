import continuation.PositiveGroundOrthogonal
import continuation.CompactPotentialFirstPositive

/-! First positive full-domain eigenstate of the genuine physical round
sphere drift Schrödinger operator. Every ground and orthogonal trial-state
condition of the compact variational theorem is discharged explicitly. -/
noncomputable section
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLCompactPotential

namespace DFLDriftBaseline
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance
omit [Fact (finrank ℝ E=n+1)] [NeZero n] in
private theorem physicalSphereConnected (hfin : finrank ℝ E=n+1) (hn : 0<n) :
    ConnectedSpace (sphere (0 : E) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank,hfin]
  exact_mod_cast (show 1<n+1 by omega)

/-- Genuine first positive physical-sphere eigenfunction and full weak-H¹
Rayleigh minimum. The only inputs are the actual unit axis and the field;
zero-ground existence, positivity, simplicity and trial-state existence
are all proved, including on S¹. -/
theorem actual_physical_drift_first_positive_exists (p : E) (hp : ‖p‖ = 1) (r : ℝ) :
    ∃ (e : SmoothScalar (roundMetric (E := E) (n := n))) (lam : ℝ)
      (u : SmoothScalar (roundMetric (E := E) (n := n))),
      ‖smoothToLp (roundMetric (E := E) (n := n)) e‖=1 ∧ (∀ x,0<e.toFun x) ∧
      (∀ x,-ΔG (roundMetric (E := E) (n := n)) e.toContMDiffMap x+
        driftPotential n p r x*e.toFun x=0) ∧
      (∃ c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := n) p r) ∧
      0<lam ∧ ‖smoothToLp (roundMetric (E := E) (n := n)) u‖=1 ∧
      ⟪smoothToLp (roundMetric (E := E) (n := n)) u,
        smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 ∧
      (∀ x,-ΔG (roundMetric (E := E) (n := n)) u.toContMDiffMap x+
        driftPotential n p r x*u.toFun x=lam*u.toFun x) ∧
      (∀ W : H1Compl (roundMetric (E := E) (n := n)),
        ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
          smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 →
        lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
          potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W) ∧
      IsWeakPotentialEigenstate (roundMetric (E := E) (n := n)) (driftPotential n p r) lam
        (smoothToH1Compl (roundMetric (E := E) (n := n)) u) := by
  let g := roundMetric (E := E) (n := n)
  let _ : ConnectedSpace (sphere (0 : E) 1) := physicalSphereConnected Fact.out (NeZero.pos n)
  obtain ⟨e,hen,hep,heig,hexp,W,hWn,hWo⟩ := actual_drift_normalized_zero_orthogonal_exists (n := n) p hp r
  obtain ⟨lam,u,hl,hu,ho,he,hm,hw⟩ := positive_zero_ground_first_positive_exists g
    (driftPotentialMap (n := n) p r) e hen hep (by
      intro x
      change -ΔG g e.toContMDiffMap x+driftPotential n p r x*e.toFun x=0*e.toFun x
      simpa only [zero_mul] using heig x)
    ⟨W,norm_pos_iff.mp hWn,hWo⟩
  exact ⟨e,lam,u,hen,hep,heig,hexp,hl,hu,ho,he,hm,hw⟩

end DFLDriftBaseline
