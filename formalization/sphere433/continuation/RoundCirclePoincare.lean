import continuation.CircleSpectralLower
import continuation.SphereIsometricCoordinates
import DFLSphere433.RoundSpherePoincare
import DFLSphere433.WeakH1Completion
import DFLSphere433.RoundSphereFirstEigenspace

/-! The sharp full-domain Poincare inequality on the actual round S¹.
The positive spectral lower bound is derived from genuine periodic Fourier
analysis, then transferred through the proved closed-manifold eigenbasis.
The weak H1 formulation uses the actual distributional Riemannian gradient. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp DFLWeakH1Completion

namespace DFLRoundCircle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)]

private instance : Fact (finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
private instance : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin 1))) := ⟨by simp⟩
private instance : ConnectedSpace (sphere (0 : E) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank, (Fact.out : finrank ℝ E = 1 + 1)]
  norm_num
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

abbrev circleVolume :=
  riemannianVolumeMeasure (𝓡 1) (sphere (0 : E) 1) (roundMetric (E := E) (n := 1))

def complexPlaneIsometry : ℂ ≃ₗᵢ[ℝ] E :=
  Complex.isometryOfOrthonormal ((stdOrthonormalBasis ℝ E).reindex
    (finCongr (Fact.out : finrank ℝ E = 1 + 1)))

/-- Arbitrary two-dimensional Euclidean ambient space, actual round metric. -/
theorem round_circle_positive_eigenvalue_ge_one
    (f : C^∞⟮𝓡 1, sphere (0 : E) 1; ℝ⟯) (lam : ℝ) (hlam : 0 < lam)
    (hf : ∃ x, f x ≠ 0)
    (heig : ∀ x, ΔG (roundMetric (E := E) (n := 1)) f x = -lam * f x) :
    1 ≤ lam := by
  let e := complexPlaneIsometry (E := E)
  let Φ := DFLSphereIsometric.sphereLinearDiffeo (n := 1) e
  let F : C^∞⟮𝓡 1, DFLCircleRound.UnitRoundCircle; ℝ⟯ :=
    ⟨f ∘ Φ, f.contMDiff.comp Φ.contMDiff⟩
  apply DFLCircleRound.circle_positive_eigenvalue_ge_one F lam hlam
  · obtain ⟨x, hx⟩ := hf
    refine ⟨Φ.symm x, ?_⟩
    change f (Φ (Φ.symm x)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hx
  · intro x
    have he := DFLSphereIsometric.sphereLinearDiffeo_laplacian (n := 1) e f x
    change ΔG DFLCircleRound.circleRoundMetric F x =
      ΔG (roundMetric (E := E) (n := 1)) f (Φ x) at he
    exact he.trans (heig (Φ x))

/-- The actual compact-resolvent eigenvalues of the round S¹ have gap one. -/
theorem round_circle_actual_spectral_lower
    (i : DFLSphere.ScalarIndex (roundMetric (E := E) (n := 1)))
    (hi : 0 < laplacianEigenvalueOf i.1.val) :
    1 ≤ laplacianEigenvalueOf i.1.val := by
  let g := roundMetric (E := E) (n := 1)
  obtain ⟨s, hs, hse⟩ := laplacianEigenfunction_smooth_representative g i
  have hnonzero : ∃ x, s.toFun x ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : resolventEigenbasisSigma g i = 0 := by
      apply Lp.ext
      exact (hs.trans (ae_of_all _ h)).trans
        (Lp.coeFn_zero ℝ 2 circleVolume).symm
    have hnorm : ‖resolventEigenbasisSigma g i‖ = 1 := by
      rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
      exact (resolventEigenbasisVec_orthonormal g).norm_eq_one i
    rw [hzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  exact round_circle_positive_eigenvalue_ge_one s.toContMDiffMap
    (laplacianEigenvalueOf i.1.val) hi hnonzero hse

/-- Every mean-zero vector in the actual full smooth H1 completion. -/
theorem round_circle_h1_poincare
    (U : H1Compl (roundMetric (E := E) (n := 1)))
    (hmean : (∫ x : sphere (0 : E) 1,
      (H1ComplToLp (roundMetric (E := E) (n := 1)) U) x ∂circleVolume) = 0) :
    ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖ ^ 2 ≤
      ‖U‖ ^ 2 - ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖ ^ 2 := by
  simpa only [one_mul] using DFLSphere.h1_poincare_of_actual_spectral_lower
    (roundMetric (E := E) (n := 1)) 1 round_circle_actual_spectral_lower U
    (DFLSphere.mean_zero_orthogonal_zero_eigenvectors
      (roundMetric (E := E) (n := 1)) U hmean)

/-- True distributional weak H1 functions, with their given L2 weak gradient. -/
theorem round_circle_weakH1_poincare (u : sphere (0 : E) 1 → ℝ)
    (hu : MemLp u 2 circleVolume)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 1) x)
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := 1)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := 1)) G) 2 circleVolume)
    (hmean : (∫ x, u x ∂circleVolume) = 0) :
    (∫ x, u x ^ 2 ∂circleVolume) ≤
      ∫ x, (roundMetric (E := E) (n := 1)).inner x (G x) (G x) ∂circleVolume := by
  let g := roundMetric (E := E) (n := 1)
  obtain ⟨U, hU, hE⟩ := weakH1_function_exists_completion_energy g u hu G hG hGn
  have hm : (∫ x, (H1ComplToLp g U) x ∂circleVolume) = 0 :=
    (integral_congr_ae hU).trans hmean
  have hn : ‖H1ComplToLp g U‖ ^ 2 = ∫ x, u x ^ 2 ∂circleVolume := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx, Real.inner_apply, pow_two]
  have h := round_circle_h1_poincare U hm
  rw [hE, hn] at h
  exact h

/-- The first smooth eigenspace consists exactly of actual ambient coordinates. -/
theorem round_circle_first_eigenfunction_iff_linear
    (f : C^∞⟮𝓡 1, sphere (0 : E) 1; ℝ⟯) :
    (∀ x, ΔG (roundMetric (E := E) (n := 1)) f x = -f x) ↔
      ∃ a : E, ∀ x, f x = ⟪a, (x : E)⟫_ℝ := by
  simpa only [Nat.cast_one, neg_one_mul] using
    DFLFirstEigenspace.round_first_eigenfunction_iff_linear (n := 1) f

end DFLRoundCircle
