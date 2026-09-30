import DFLSphere433.H1SpectralPoincare
import DifferentialGeometry.Analysis.Elliptic.LichnerowiczSpectral
import DifferentialGeometry.Analysis.Elliptic.HarmonicRigidity
import DifferentialGeometry.Geometry.Curvature.RoundSphere
import Mathlib.Analysis.Normed.Module.Connected

/-!
Zero-field Poincaré lower bound on the true round sphere, for every
mean-zero vector of the actual full smooth H¹ completion. No spectral
gap or eigenvalue lower bound is supplied as a hypothesis.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem h1_smooth_energy (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    ‖smoothToH1Compl g f‖ ^ 2 - ‖H1ComplToLp g (smoothToH1Compl g f)‖ ^ 2 =
      ∫ x : M, g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)
        ∂riemannianVolumeMeasure I M g := by
  have hfull : ‖smoothToH1Compl g f‖ ^ 2 =
      smoothScalarH1Inner f f := by
    rw [← real_inner_self_eq_norm_sq, inner_smoothToH1Compl_smoothToH1Compl]
  have hnorm : ‖smoothToLp g f‖ ^ 2 = ∫ x : M, f.toFun x * f.toFun x
      ∂riemannianVolumeMeasure I M g := f.norm_smoothToLp_sq
  rw [hfull, H1ComplToLp_smoothToH1Compl, hnorm]
  unfold smoothScalarH1Inner
  change (∫ x : M, f.toFun x * f.toFun x ∂riemannianVolumeMeasure I M g) +
      (∫ x : M, g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)
        ∂riemannianVolumeMeasure I M g) -
      (∫ x : M, f.toFun x * f.toFun x ∂riemannianVolumeMeasure I M g) = _
  ring

theorem mean_zero_orthogonal_zero_eigenvectors
    (g : SmoothRiemannianMetric I M) (u : H1Compl g)
    (hmean : (∫ x : M, (H1ComplToLp (I := I) (M := M) g u) x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0)
    (i : ScalarIndex g) (hzero : laplacianEigenvalueOf i.1.val = 0) :
    ⟪resolventEigenbasisSigma (I := I) (M := M) g i,
      H1ComplToLp (I := I) (M := M) g u⟫_ℝ = 0 := by
  obtain ⟨s, hs, hse⟩ := laplacianEigenfunction_smooth_representative
    (I := I) (M := M) g i
  have hharm : ∀ x : M, ΔG (I := I) g s.toContMDiffMap x = 0 := by
    intro x
    change ΔG (I := I) g ⟨s.toFun, s.smooth⟩ x = 0
    simpa only [hzero, neg_zero, zero_mul] using hse x
  obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero g s.toContMDiffMap hharm
  have hconst : (resolventEigenbasisSigma (I := I) (M := M) g i : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] (fun _ => c) := by
    change (resolventEigenbasisSigma (I := I) (M := M) g i : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] s.toFun at hs
    exact hs.trans (ae_of_all _ hc)
  rw [L2.inner_def]
  calc
    _ = ∫ x : M, c * (H1ComplToLp (I := I) (M := M) g u) x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      apply integral_congr_ae
      filter_upwards [hconst] with x hx
      rw [hx, Real.inner_apply]
    _ = c * ∫ x : M, (H1ComplToLp (I := I) (M := M) g u) x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := integral_const_mul _ _
    _ = 0 := by rw [hmean, mul_zero]

theorem h1_poincare_of_positive_ricci
    (g : SmoothRiemannianMetric I M) (hn : 2 ≤ Module.finrank ℝ E)
    (K : ℝ) (hK : 0 < K)
    (hRic : ∀ x : M, ∀ X : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * K * g.inner x X X ≤
        ricciTensor (I := I) g x X X)
    (u : H1Compl g)
    (hmean : (∫ x : M, (H1ComplToLp (I := I) (M := M) g u) x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0) :
    ((Module.finrank ℝ E : ℝ) * K) * ‖H1ComplToLp (I := I) (M := M) g u‖ ^ 2 ≤
      ‖u‖ ^ 2 - ‖H1ComplToLp (I := I) (M := M) g u‖ ^ 2 := by
  apply h1_poincare_of_actual_spectral_lower g ((Module.finrank ℝ E : ℝ) * K)
  · intro i hi
    exact lichnerowicz_spectral_eigenvalue_ge_dim_mul_curvature_of_closed
      g hn hK hRic i hi
  · exact mean_zero_orthogonal_zero_eigenvectors g u hmean

abbrev RoundAmbient (k : ℕ) := EuclideanSpace ℝ (Fin (k + 3))
abbrev RoundSphere (k : ℕ) := sphere (0 : RoundAmbient k) 1

instance (k : ℕ) : Fact (Module.finrank ℝ (RoundAmbient k) = k + 2 + 1) :=
  ⟨by simp [RoundAmbient]⟩

instance (k : ℕ) : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 2)))) :=
  ⟨by simp⟩

instance (k : ℕ) : ConnectedSpace (RoundSphere k) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank]
  simp only [RoundAmbient, finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < k + 3 by omega)

def roundSphereMetric (k : ℕ) : SmoothRiemannianMetric (𝓡 (k + 2)) (RoundSphere k) :=
  roundMetric (E := RoundAmbient k) (n := k + 2)

/-- Original closed round sphere `S^(k+2)`, all mean-zero H¹ functions,
with the ordinary intrinsic Dirichlet energy of its full form domain. -/
theorem roundSphere_h1_poincare (k : ℕ) (u : H1Compl (roundSphereMetric k))
    (hmean : (∫ x : RoundSphere k,
      (H1ComplToLp (roundSphereMetric k) u) x
      ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) = 0) :
    (k + 2 : ℝ) * ‖H1ComplToLp (roundSphereMetric k) u‖ ^ 2 ≤
      ‖u‖ ^ 2 - ‖H1ComplToLp (roundSphereMetric k) u‖ ^ 2 := by
  have hn : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 2))) := by simp
  have hRic : ∀ x : RoundSphere k, ∀ X : TangentSpace (𝓡 (k + 2)) x,
      ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 2))) : ℝ) - 1) * 1 *
        (roundSphereMetric k).inner x X X ≤
      ricciTensor (I := 𝓡 (k + 2)) (roundSphereMetric k) x X X := by
    intro x X
    unfold roundSphereMetric
    rw [ricciTensor_roundSphere]
    simp
  simpa using h1_poincare_of_positive_ricci (roundSphereMetric k) hn 1 (by norm_num)
    hRic u hmean

end DFLSphere

#print axioms DFLSphere.roundSphere_h1_poincare
