import continuation.SmoothAbsoluteH1
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Classical C² functions on compact boundaryless Riemannian manifolds
enter the actual distributional weak H¹ domain and the smooth H¹ completion.
The proof uses the existing C¹ Lipschitz integration by parts theorem. -/
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp DifferentialGeometry.Analysis.Laplacian
open DFLWeakH1Completion

namespace DFLC2WeakH1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The genuine classical gradient is the distributional weak gradient of
every C¹ function, using actual intrinsic integration by parts. -/
theorem contMDiff_one_hasWeakGrad (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    HasWeakRiemannianGradLp g f (gradientFun g f) := by
  obtain ⟨C, _, hC⟩ := exists_riemannian_lipschitz_of_contMDiff g hf
  have hpair : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      (fun x => g.inner x (gradientFun g f x) (X x)) = tangentSectionAction X f := by
    intro X
    funext x
    rw [inner_gradientFun, tangentSectionAction_def, mvfderiv_real_eq_mfderiv]
    rfl
  constructor
  · intro X
    obtain ⟨hi, _⟩ :=
      integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
        g X (HasCompactSupport.of_compactSpace _) hC
    rw [hpair]
    exact hi.aestronglyMeasurable
  · intro X hX
    obtain ⟨_, hi⟩ :=
      integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
        g X hX hC
    rw [hpair]
    exact hi

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
/-- The actual squared gradient norm of a C² function is continuous. -/
theorem contMDiff_two_gradient_energy_continuous (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    Continuous (fun x => g.inner x (gradientFun g f x) (gradientFun g f x)) := by
  have hG : ContMDiff I I.tangent 1
      (fun x => TotalSpace.mk' E x (gradientFun g f x)) := by
    intro x
    exact gradientFun_contMDiffAt_one g hf.contMDiffAt
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := Continuous.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := gradientFun g f) (w := gradientFun g f)
    hG.continuous hG.continuous
  refine h.congr ?_
  intro x
  rfl

omit [I.Boundaryless] in
/-- C² functions and their actual classical gradients have finite L² norm. -/
theorem contMDiff_two_memWeakH1 (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    MemLp f 2 (riemannianVolumeMeasure I M g) ∧
      MemLp (metricNorm g (gradientFun g f)) 2 (riemannianVolumeMeasure I M g) := by
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  constructor
  · exact hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hN := Real.continuous_sqrt.comp
      (contMDiff_two_gradient_energy_continuous g f hf)
    exact hN.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The actual smooth H¹ completion represents a C² function with its exact
classical Dirichlet energy, without requiring a C∞ representative. -/
theorem contMDiff_two_exists_completion_energy [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    ∃ U : H1Compl g,
      (H1ComplToLp g U : M → ℝ) =ᵐ[riemannianVolumeMeasure I M g] f ∧
      ‖U‖ ^ 2 - ‖H1ComplToLp g U‖ ^ 2 =
        ∫ x, g.inner x (gradientFun g f x) (gradientFun g f x)
          ∂riemannianVolumeMeasure I M g := by
  obtain ⟨hfL, hGL⟩ := contMDiff_two_memWeakH1 g f hf
  exact DFLWeakH1Completion.weakH1_function_exists_completion_energy g f hfL
    (gradientFun g f) (contMDiff_one_hasWeakGrad g f (hf.of_le (by norm_num))) hGL

/-- A nonzero continuous classical function is also nonzero in actual L²,
because the Riemannian volume gives positive mass to nonempty open sets. -/
theorem contMDiff_two_exists_nonzero_completion_energy [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hfne : f ≠ 0) :
    ∃ U : H1Compl g,
      (H1ComplToLp g U : M → ℝ) =ᵐ[riemannianVolumeMeasure I M g] f ∧
      0 < ‖H1ComplToLp g U‖ ∧
      ‖U‖ ^ 2 - ‖H1ComplToLp g U‖ ^ 2 =
        ∫ x, g.inner x (gradientFun g f x) (gradientFun g f x)
          ∂riemannianVolumeMeasure I M g := by
  obtain ⟨U, hU, hE⟩ := contMDiff_two_exists_completion_energy g f hf
  let μ := riemannianVolumeMeasure I M g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  refine ⟨U, hU, norm_pos_iff.mpr ?_, hE⟩
  intro hz
  have hzAE := Lp.coeFn_zero ℝ 2 μ
  rw [← hz] at hzAE
  exact hfne (MeasureTheory.Measure.eq_of_ae_eq (hU.symm.trans hzAE) hf.continuous continuous_const)

end DFLC2WeakH1
