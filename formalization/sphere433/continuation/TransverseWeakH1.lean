import continuation.TransverseSphereMode
import continuation.CompactC2WeakH1

/-! The actual transverse eigenfunction belongs to distributional weak H¹
and has a nonzero representative in the true smooth H¹ completion. -/
noncomputable section
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFL.Spectral DFLSphere DFLWeakH1Completion DFLC2WeakH1

namespace DFLTransverseSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

omit [NeZero n] in
/-- The actual classical transverse mode has a distributional gradient
and belongs to the original weak H¹ domain. -/
theorem transverseMode_memWeakH1 (p a : E) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2 (transverseMode p a v) := by
  let g := roundMetric (E := E) (n := n)
  have hf := transverseMode_contMDiff (n := n) p a v hv
  obtain ⟨hfL,hGL⟩ := contMDiff_two_memWeakH1 g (transverseMode p a v) hf
  exact ⟨hfL,gradientFun g (transverseMode p a v),
    contMDiff_one_hasWeakGrad g _ (hf.of_le (by norm_num)),hGL⟩

/-- A nonzero transverse mode enters the actual smooth H¹ completion with
positive L² mass and its exact classical gradient energy. -/
theorem transverseMode_exists_completion_energy (p a : E)
    (ha : ‖a‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hv0 : 0 < v 0) :
    ∃ U : H1Compl (roundMetric (E := E) (n := n)),
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          transverseMode p a v ∧
      0 < ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ∧
      ‖U‖^2-‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 =
        ∫ x, (roundMetric (E := E) (n := n)).inner x
          (gradientFun (roundMetric (E := E) (n := n)) (transverseMode p a v) x)
          (gradientFun (roundMetric (E := E) (n := n)) (transverseMode p a v) x)
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  exact contMDiff_two_exists_nonzero_completion_energy (roundMetric (E := E) (n := n))
    (transverseMode p a v) (transverseMode_contMDiff p a v hv)
    (transverseMode_nonzero p a ha hpa v hv0)

/-- The genuine auxiliary ground eigenvalue has an actual nonzero physical
sphere weak-H¹ eigenfunction and a true completion representative. No mode
realizability, classical profile, or weak-domain hypothesis is an input. -/
theorem actual_transverse_weakH1_ground_exists (p a : E) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1)
    (hpa : ⟪a,p⟫_ℝ = 0) (r : ℝ) :
    ∃ (v : ℝ → ℝ) (U : H1Compl (roundMetric (E := E) (n := n))),
      ContDiff ℝ 2 v ∧ (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm (n+2) r v = 1 ∧
      MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2 (transverseMode p a v) ∧
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          transverseMode p a v ∧
      0 < ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ∧
      ‖U‖^2-‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 =
        ∫ x, (roundMetric (E := E) (n := n)).inner x
          (gradientFun (roundMetric (E := E) (n := n)) (transverseMode p a v) x)
          (gradientFun (roundMetric (E := E) (n := n)) (transverseMode p a v) x)
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) ∧
      ∀ x : sphere (0 : E) 1, weightedRoundApply (n := n) p r (transverseMode p a v) x =
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*transverseMode p a v x := by
  obtain ⟨v,hv,hpos,hn,_hC,_hne,heig⟩ := actual_transverse_ground_exists (n := n) p a hp ha hpa r
  obtain ⟨U,hU,hUn,hE⟩ := transverseMode_exists_completion_energy (n := n) p a ha hpa v hv
    (hpos 0 (by norm_num))
  exact ⟨v,U,hv,hpos,hn,transverseMode_memWeakH1 p a v hv,hU,hUn,hE,heig⟩

end DFLTransverseSphere
