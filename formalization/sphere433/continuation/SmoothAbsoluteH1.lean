import DFLSphere433.WeakH1Completion
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz.Basic
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz

/-! Absolute values of smooth scalar functions belong to the actual
 distributional weak H¹ domain. The existing intrinsic Lipschitz integration
 by parts gives the weak derivative, and the pointwise gradient formula gives
 the original Dirichlet energy contraction. -/

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Analysis.Laplacian
open scoped RealInnerProductSpace

namespace DFLAbsoluteH1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] [T2Space M] in
private theorem gradFun_eq_gradientFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun g f x = gradientFun g f x := by
  apply metricFlatLinear_injective g x
  ext v
  change g.inner x (gradFun g f x) v = g.inner x (gradientFun g f x) v
  rw [inner_gradFun, inner_gradientFun]
  rfl

omit [T2Space M] in
/-- At zeros the absolute value has zero formal manifold derivative: either
it is differentiable at its local minimum, or mfderiv takes its defined zero value. -/
theorem grad_absolute_at_zero (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : M) (hx : f x = 0) : gradFun g (fun y => |f y|) x = 0 := by
  have hmin : IsLocalMin (fun y => |f y|) x := by
    apply Filter.Eventually.of_forall
    intro y
    simpa only [hx, abs_zero] using abs_nonneg (f y)
  by_cases hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => |f y|) x
  · rw [gradFun_eq_gradientFun]
    exact gradientFun_eq_zero_of_isLocalMin g hmin hd
  · exact gradFun_eq_zero_of_mfderiv_eq_zero g _ (mfderiv_zero_of_not_mdifferentiableAt hd)

omit [T2Space M] in
/-- The actual pointwise gradient formula on the positive and negative regions. -/
theorem grad_absolute_of_smooth (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    gradFun g (fun y => |f y|) x =
      if 0 < f x then gradFun g f x else if f x < 0 then -gradFun g f x else 0 := by
  classical
  by_cases hp : 0 < f x
  · have heq : (fun y => |f y|) =ᶠ[𝓝 x] (f : M → ℝ) := by
      filter_upwards [(f.contMDiff.continuous.tendsto x).eventually (Ioi_mem_nhds hp)] with y hy
      exact abs_of_pos hy
    rw [if_pos hp, gradFun_def, gradFun_def, heq.mfderiv_eq]
  · rw [if_neg hp]
    by_cases hn : f x < 0
    · have heq : (fun y => |f y|) =ᶠ[𝓝 x] -(f : M → ℝ) := by
        filter_upwards [(f.contMDiff.continuous.tendsto x).eventually (Iio_mem_nhds hn)] with y hy
        exact abs_of_neg hy
      rw [if_pos hn]
      have hg : gradFun g (fun y => |f y|) x = gradFun g (-(f : M → ℝ)) x := by
        rw [gradFun_def, gradFun_def, heq.mfderiv_eq]
      rw [hg, gradFun_eq_gradientFun, gradientFun_neg g (f.contMDiff.mdifferentiable (by simp) x),
        ← gradFun_eq_gradientFun]
    · rw [if_neg hn]
      exact grad_absolute_at_zero g _ x (le_antisymm (le_of_not_gt hp) (le_of_not_gt hn))

omit [T2Space M] in
/-- The exact zero-level-set formula implies the Dirichlet energy contraction. -/
theorem grad_absolute_energy (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    g.inner x (gradFun g (fun y => |f y|) x) (gradFun g (fun y => |f y|) x) =
      if f x = 0 then 0 else g.inner x (gradFun g f x) (gradFun g f x) := by
  classical
  by_cases hz : f x = 0
  · rw [if_pos hz, grad_absolute_at_zero g _ x hz, map_zero]
  · rw [if_neg hz, grad_absolute_of_smooth]
    by_cases hp : 0 < f x
    · simp only [if_pos hp]
    · have hn : f x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      simp only [if_neg hp, if_pos hn]
      have hneg (v w : TangentSpace I x) : g.inner x (-v) (-w) = g.inner x v w := by
        have h₁ := (g.inner x).map_neg v
        have h₂ := (g.inner x v).map_neg w
        rw [h₁, neg_apply, h₂, neg_neg]
      exact hneg _ _

variable [CompactSpace M]

/-- Original distributional weak gradient of |f|, using the upstream intrinsic
Lipschitz integration by parts rather than a assumed composition rule. -/
theorem smooth_absolute_hasWeakGrad (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    HasWeakRiemannianGradLp g (fun x => |f x|) (fun x => gradFun g (fun y => |f y|) x) := by
  obtain ⟨C, _, hC⟩ := exists_riemannian_lipschitz_of_contMDiff g
    (f.contMDiff.of_le (by simp))
  have habs : ∀ x y, edist (|f x|) (|f y|) ≤ (C : ℝ≥0∞)*riemannianEDistOf g x y := by
    intro x y
    exact (show edist (|f x|) (|f y|) ≤ edist (f x) (f y) from
      by
        rw [edist_dist, edist_dist]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.norm_eq_abs, Real.dist_eq] using dist_norm_norm_le (f x) (f y)).trans (hC x y)
  have hpair : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      (fun x => g.inner x (gradFun g (fun y => |f y|) x) (X x)) =
        tangentSectionAction X (fun x => |f x|) := by
    intro X
    funext x
    rw [inner_gradFun, tangentSectionAction_def]
  constructor
  · intro X
    obtain ⟨hi, _⟩ := integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
      g X (HasCompactSupport.of_compactSpace _) habs
    rw [hpair]
    exact hi.aestronglyMeasurable
  · intro X hX
    obtain ⟨_, hi⟩ := integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
      g X hX habs
    rw [hpair]
    exact hi

/-- |f| and its actual weak gradient have finite L² norm. -/
theorem smooth_absolute_memWeakH1 (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    MemLp (fun x => |f x|) 2 (riemannianVolumeMeasure I M g) ∧
      MemLp (fun x => Real.sqrt (g.inner x (gradFun g (fun y => |f y|) x)
        (gradFun g (fun y => |f y|) x))) 2 (riemannianVolumeMeasure I M g) := by
  classical
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hf : MemLp (f : M → ℝ) 2 (riemannianVolumeMeasure I M g) :=
    f.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · simpa only [Real.norm_eq_abs] using hf.norm
  · have hN : Continuous (fun x => Real.sqrt (g.inner x (gradFun g f x) (gradFun g f x))) :=
      Real.continuous_sqrt.comp (normGradSqFun_contMDiff g f.contMDiff).continuous
    have hNl : MemLp (fun x => Real.sqrt (g.inner x (gradFun g f x) (gradFun g f x))) 2
        (riemannianVolumeMeasure I M g) := hN.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
      (HasCompactSupport.of_compactSpace _)
    have hmeas : MeasurableSet {x : M | f x ≠ 0} :=
      (isClosed_singleton.preimage f.contMDiff.continuous).measurableSet.compl
    have heq : (fun x => Real.sqrt (g.inner x (gradFun g (fun y => |f y|) x)
        (gradFun g (fun y => |f y|) x))) =
      {x : M | f x ≠ 0}.indicator (fun x => Real.sqrt (g.inner x (gradFun g f x) (gradFun g f x))) := by
      funext x
      rw [grad_absolute_energy]
      by_cases hx : f x = 0 <;> simp [hx]
    rw [heq]
    exact hNl.indicator hmeas

/-- The absolute value of any actual smooth function has a true H¹ completion
representative, with unchanged mass and no greater Dirichlet energy. -/
theorem smooth_absolute_exists_completion [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    ∃ A : H1Compl g,
      (H1ComplToLp g A : M → ℝ) =ᵐ[riemannianVolumeMeasure I M g] (fun x => |f.toFun x|) ∧
      ‖H1ComplToLp g A‖ = ‖smoothToLp g f‖ ∧
      ‖A‖^2-‖H1ComplToLp g A‖^2 ≤
        ∫ x, g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)
          ∂riemannianVolumeMeasure I M g := by
  let μ := riemannianVolumeMeasure I M g
  obtain ⟨hf,hG⟩ := smooth_absolute_memWeakH1 g f.toContMDiffMap
  obtain ⟨A,hA,hAE⟩ := DFLWeakH1Completion.weakH1_function_exists_completion_energy g
    (fun x => |f.toFun x|) hf (fun x => gradFun g (fun y => |f.toFun y|) x)
      (smooth_absolute_hasWeakGrad g f.toContMDiffMap) hG
  have hmass : ‖H1ComplToLp g A‖^2 = ‖smoothToLp g f‖^2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA,f.memLp_two.coeFn_toLp] with x ha hf
    have hff : (smoothToLp g f : M → ℝ) x = f.toFun x := hf
    simp only [ha,hff,RCLike.inner_apply,conj_trivial]
    nlinarith [sq_abs (f.toFun x)]
  refine ⟨A,hA,?_,?_⟩
  · nlinarith [norm_nonneg (H1ComplToLp g A),norm_nonneg (smoothToLp g f)]
  · rw [hAE]
    have hfin : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
    have hc : Continuous (fun x => g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)) :=
      (normGradSqFun_contMDiff g f.smooth).continuous
    have hi : Integrable (fun x => g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)) μ :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hm : MeasurableSet {x : M | f.toFun x ≠ 0} :=
      (isClosed_singleton.preimage f.smooth.continuous).measurableSet.compl
    have heq : (fun x => g.inner x (gradFun g (fun y => |f.toFun y|) x)
        (gradFun g (fun y => |f.toFun y|) x)) =
      {x : M | f.toFun x ≠ 0}.indicator
        (fun x => g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x)) := by
      funext x
      have hgrad := grad_absolute_energy g f.toContMDiffMap x
      change g.inner x (gradFun g (fun y => |f.toFun y|) x)
        (gradFun g (fun y => |f.toFun y|) x) =
          if f.toFun x = 0 then 0 else g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x) at hgrad
      rw [hgrad]
      by_cases hx : f.toFun x = 0 <;> simp [hx]
    apply integral_mono (heq.symm ▸ hi.indicator hm) hi
    intro x
    have hgrad := grad_absolute_energy g f.toContMDiffMap x
    change g.inner x (gradFun g (fun y => |f.toFun y|) x)
      (gradFun g (fun y => |f.toFun y|) x) =
        if f.toFun x = 0 then 0 else g.inner x (gradFun g f.toFun x) (gradFun g f.toFun x) at hgrad
    dsimp only
    rw [hgrad]
    split_ifs
    · exact metric_inner_self_nonneg g _ _
    · exact le_rfl

end DFLAbsoluteH1
