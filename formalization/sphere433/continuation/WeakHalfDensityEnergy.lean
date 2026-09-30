import continuation.HalfDensityEnergy
import DFLSphere433.WeakH1Completion
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakProduct

/-! The original half-density identity on the distributional weak H¹ domain.
The cross term is extended using the proved intrinsic smooth density theorem.
Neither smoothness of the observable nor smoothness of its weak gradient is
an input to the resulting mass and energy correspondence. -/
noncomputable section
set_option maxHeartbeats 1600000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFLWeakH1Completion DFLCompactPotential DFLSpectralCoordinates DFLLatitudeOperator

namespace DFLWeakHalfDensity

section Compact
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Finite ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [T2Space M] in
private theorem gradFun_eq_gradientFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun g f x = gradientFun g f x := by
  apply metricFlatLinear_injective g x
  ext v
  change g.inner x (gradFun g f x) v = g.inner x (gradientFun g f x) v
  rw [inner_gradFun,inner_gradientFun]
  rfl

/-- Actual metric L² convergence gives L² convergence of pairing with any
smooth tangent test field. The weak field need not be a smooth section. -/
theorem metric_pairing_L2_tendsto (g : SmoothRiemannianMetric I M)
    {V : ℕ → ∀ x : M, TangentSpace I x} {G : ∀ x : M, TangentSpace I x}
    (X : Cₛ^∞⟮I; F, (TangentSpace I : M → Type _)⟯)
    (hmetric : Tendsto (fun j => eLpNorm (metricNorm g (fun x => V j x-G x)) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => g.inner x (V j x) (X x)-g.inner x (G x) (X x))
      2 (riemannianVolumeMeasure I M g)) atTop (𝓝 0) := by
  have hXcont : Continuous (metricNorm g (fun x => X x)) :=
    Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g X X)
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hXcont.continuousOn
  have hlim : Tendsto (fun j => ENNReal.ofReal C * eLpNorm
      (metricNorm g (fun x => V j x-G x)) 2 (riemannianVolumeMeasure I M g)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hmetric (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro j
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards with x
  dsimp only [metricNorm]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have heq : g.inner x (V j x) (X x)-g.inner x (G x) (X x)=
      g.inner x (V j x-G x) (X x) := by rw [map_sub,sub_apply]
  rw [heq]
  calc
    _ ≤ metricNorm g (fun x => V j x-G x) x*metricNorm g (fun x => X x) x :=
      Analysis.Sobolev.EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt g x _ _
    _ ≤ metricNorm g (fun x => V j x-G x) x*C := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      simpa only [metricNorm,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hC x (mem_univ x)
    _ = _ := mul_comm _ _

end Compact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

omit [NeZero n] in
/-- Distributional weak H¹ is preserved in both directions by the genuine
positive half-density multiplier on the whole sphere. -/
theorem half_density_weakH1_iff (p : E) (r : ℝ) (u : sphere (0 : E) 1 → ℝ) :
    MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2
      (fun x => DFLPhysicalHalfDensity.halfFactor p r x*u x) ↔
    MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2 u := by
  constructor
  · intro hu
    have hi := hu.smooth_mul (by norm_num : (1 : ℝ≥0∞)≤2)
      (DFLPhysicalHalfDensity.halfFactor_smooth (n := n) p (-r))
    have heq : (fun x : sphere (0 : E) 1 => DFLPhysicalHalfDensity.halfFactor p (-r) x*
        (DFLPhysicalHalfDensity.halfFactor p r x*u x))=u := by
      funext x
      rw [← mul_assoc,mul_comm (DFLPhysicalHalfDensity.halfFactor p (-r) x),
        DFLPhysicalHalfDensity.halfFactor_cancel,one_mul]
    rwa [heq] at hi
  · intro hu
    exact hu.smooth_mul (by norm_num : (1 : ℝ≥0∞)≤2)
      (DFLPhysicalHalfDensity.halfFactor_smooth (n := n) p r)

/-- The original smooth cross-term cancellation holds for every L² weak
gradient. It is a limit of the genuine smooth identities, not a domain
assumption or a formal integration by parts on an unproved test class. -/
theorem half_density_weak_cross_term (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n))))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))) :
    (∫ x, 2*Real.exp (r*⟪p,(x : E)⟫_ℝ)*u x*
      (roundMetric (E := E) (n := n)).inner x (G x)
        (gradFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) =
    -(∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*
      (r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)*(u x)^2
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let _ : IsFiniteMeasure mu := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let rho := fun x : sphere (0 : E) 1 => Real.exp (r*⟪p,(x : E)⟫_ℝ)
  have hrho : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ rho :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul (innerCoordFun (n := n) p).contMDiff)
  let X := smoothSmul rho hrho (gradG g (innerCoordFun (n := n) p))
  have hX (x : sphere (0 : E) 1) : X x=rho x • gradFun g (innerCoordFun (n := n) p) x := by
    rw [smoothSmul_apply,grad_g_apply]
  obtain ⟨f,hf,hscalar,_hpoint,hmetric⟩ := hG.exists_smooth_metricL2_approx hu hGn
  have hfLp (j : ℕ) : MemLp (f j) 2 mu :=
    (MemW1pIntrinsicLp_of_contMDiff g 2 (hf j)).1
  have hgLp (j : ℕ) : MemLp (fun x => g.inner x (gradFun g (f j) x) (X x)) 2 mu :=
    ((Analysis.Sobolev.Equivalence.hasWeakRiemannianGradLp_gradFun g (hf j))).pairing_memLp
      (smoothMetricGrad_memLp g ⟨f j,hf j⟩) X
  have hGLp : MemLp (fun x => g.inner x (G x) (X x)) 2 mu := hG.pairing_memLp hGn X
  have hpair := metric_pairing_L2_tendsto g X hmetric
  have hleft := (Analysis.Integration.tendsto_integral_mul_of_eLpNorm_two_two
    hfLp hgLp hu hGLp hscalar hpair).const_mul 2
  let D := fun x : sphere (0 : E) 1 => rho x*
    (r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)
  have hDc : Continuous D := by
    unfold D rho
    fun_prop
  have hDtop : MemLp D ⊤ mu :=
    hDc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright := (Analysis.Integration.tendsto_integral_weighted_sq_of_eLpNorm_two
    hfLp hu hDtop hscalar).neg
  have heq (j : ℕ) : 2*(∫ x, f j x*g.inner x (gradFun g (f j) x) (X x) ∂mu)=
      -(∫ x, D x*(f j x)^2 ∂mu) := by
    rw [← integral_const_mul]
    have hcancel := DFLPhysicalHalfDensity.half_density_cross_term p hp r (f j)
      ((hf j).of_le (by decide))
    convert hcancel using 1
    congr 1
    funext x
    rw [hX]
    simp only [map_smul,smul_eq_mul]
    dsimp only [rho,g]
    change 2*(f j x*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*
      (roundMetric (E := E) (n := n)).inner x (gradFun (roundMetric (E := E) (n := n)) (f j) x)
      (gradFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x))) = _
    rw [gradFun_eq_gradientFun,gradFun_eq_gradientFun]
    ring
  have hleft' : Tendsto (fun j => -(∫ x, D x*(f j x)^2 ∂mu)) atTop
      (𝓝 (2*(∫ x, u x*g.inner x (G x) (X x) ∂mu))) := by
    simpa only [heq] using hleft
  have hlim := tendsto_nhds_unique hleft' hright
  rw [← integral_const_mul] at hlim
  convert hlim using 1
  congr 1
  funext x
  rw [hX]
  simp only [map_smul,smul_eq_mul]
  dsimp only [rho]
  ring

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The actual distributional gradient supplied by the smooth Leibniz rule. -/
def halfDensityWeakGradient (p : E) (r : ℝ) (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x) :
    ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x := fun x =>
  DFLPhysicalHalfDensity.halfFactor p r x • G x+
    u x • gradFun (roundMetric (E := E) (n := n)) (DFLPhysicalHalfDensity.halfFactor p r) x

/-- Exact original weighted Dirichlet energy after half density for an
arbitrary distributional weak H¹ observable on the genuine whole sphere. -/
theorem half_density_weak_integral_energy (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n))))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))) :
    (∫ x, (roundMetric (E := E) (n := n)).inner x
      (halfDensityWeakGradient p r u G x) (halfDensityWeakGradient p r u G x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))+
    (∫ x, DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*
      (DFLPhysicalHalfDensity.halfFactor p r x*u x)^2
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) =
    ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(roundMetric (E := E) (n := n)).inner x (G x) (G x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let h := DFLPhysicalHalfDensity.halfFactor p r
  let rho := fun x : sphere (0 : E) 1 => Real.exp (r*⟪p,(x : E)⟫_ℝ)
  let t := innerCoordFun (n := n) p
  let Z := halfDensityWeakGradient p r u G
  let C := fun x => 2*rho x*u x*g.inner x (G x) (gradFun g t x)
  let D := fun x => rho x*(r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)*(u x)^2
  let _ : IsFiniteMeasure mu := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hh := DFLPhysicalHalfDensity.halfFactor_smooth (n := n) p r
  obtain ⟨hhu,_hw,hZn⟩ := hG.smooth_mul_witness (by norm_num : (1 : ℝ≥0∞)≤2) hu hGn hh
  have hmetricInt {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
      (hY : MemLp (metricNorm g Y) 2 mu) : Integrable (fun x => g.inner x (Y x) (Y x)) mu := by
    have hid (x : sphere (0 : E) 1) : metricNorm g Y x*metricNorm g Y x=g.inner x (Y x) (Y x) := by
      rw [← pow_two]
      exact Real.sq_sqrt (inner_self_nonneg g x _)
    exact (hY.integrable_mul hY).congr (Eventually.of_forall hid)
  have hZI : Integrable (fun x => g.inner x (Z x) (Z x)) mu := hmetricInt hZn
  have hrho : Continuous rho := by unfold rho; fun_prop
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hrho.continuousOn
  have hGI : Integrable (fun x => rho x*g.inner x (G x) (G x)) mu :=
    (hmetricInt hGn).bdd_mul hrho.aestronglyMeasurable (Eventually.of_forall fun x => hB x (mem_univ x))
  have hVc : Continuous (DFLPhysicalHalfDensity.physicalPotential (n := n) p r) := by
    unfold DFLPhysicalHalfDensity.physicalPotential
    fun_prop
  have hVtop : MemLp (DFLPhysicalHalfDensity.physicalPotential (n := n) p r) ⊤ mu :=
    hVc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hVhu : MemLp (fun x => DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(h x*u x)) 2 mu := hhu.mul' hVtop
  have hVI : Integrable (fun x => DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(h x*u x)^2) mu := by
    exact (hVhu.integrable_mul hhu).congr (Eventually.of_forall fun x => by
      change (DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(h x*u x))*(h x*u x)=_
      ring)
  have hDc : Continuous (fun x => rho x*(r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)) := by
    unfold rho
    fun_prop
  have hDtop := hDc.memLp_of_hasCompactSupport (μ := mu) (p := ⊤) (HasCompactSupport.of_compactSpace _)
  have hDu : MemLp (fun x => rho x*(r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)*u x) 2 mu := hu.mul' hDtop
  have hDI : Integrable D mu :=
    (hDu.integrable_mul hu).congr (Eventually.of_forall fun x => by
      dsimp only [D,Pi.mul_apply]
      ring)
  have hPtop : MemLp (fun x => 2*rho x) ⊤ mu :=
    (continuous_const.mul hrho).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTLp := hG.pairing_memLp hGn (gradG g t)
  have hPu : MemLp (fun x => 2*rho x*u x) 2 mu := hu.mul' hPtop
  have hCI : Integrable C mu :=
    (hPu.integrable_mul hTLp).congr (Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply,C]
      rw [grad_g_apply])
  have hcancel : (∫ x, C x ∂mu)=-(∫ x, D x ∂mu) := half_density_weak_cross_term p hp r u G hu hG hGn
  have hpoint (x : sphere (0 : E) 1) : g.inner x (Z x) (Z x)+
      DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(h x*u x)^2 =
      rho x*g.inner x (G x) (G x)+r/2*(C x+D x) := by
    have hhG : gradFun g h x=(r/2*h x) • gradFun g t x := by
      rw [gradFun_eq_gradientFun,gradFun_eq_gradientFun]
      exact DFLPhysicalHalfDensity.halfFactor_gradient p r x
    have htG : g.inner x (gradFun g t x) (gradFun g t x)=1-⟪p,(x : E)⟫_ℝ^2 := by
      rw [gradFun_eq_gradientFun]
      exact latitude_gradient_norm_sq p hp x
    change g.inner x (h x • G x+u x • gradFun g h x) (h x • G x+u x • gradFun g h x)+_= _
    rw [hhG]
    simp only [map_add,add_apply,map_smul,smul_apply,smul_eq_mul]
    rw [g.symm x (gradFun g t x) (G x),htG]
    have hs : (h x)^2=rho x := DFLPhysicalHalfDensity.halfFactor_square p r x
    have hsq : (h x*u x)^2=rho x*(u x)^2 := by rw [mul_pow,hs]
    rw [hsq]
    dsimp only [DFLPhysicalHalfDensity.physicalPotential,C,D]
    change _ = rho x*g.inner x (G x) (G x)+r/2*(2*rho x*u x*g.inner x (G x) (gradFun g t x)+
      rho x*(r*(1-⟪p,(x : E)⟫_ℝ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)*(u x)^2)
    ring_nf
    rw [hs]
    ring
  rw [← integral_add hZI hVI,integral_congr_ae (Eventually.of_forall hpoint)]
  have hCDI : Integrable (fun x => C x+D x) mu := hCI.add hDI
  rw [integral_add (f := fun x => rho x*g.inner x (G x) (G x))
    (g := fun x => r/2*(C x+D x)) hGI (hCDI.const_mul (r/2)),integral_const_mul,
    integral_add (f := C) (g := D) hCI hDI,hcancel]
  change (∫ x, rho x*g.inner x (G x) (G x) ∂mu)+r/2*(-(∫ x, D x ∂mu)+(∫ x, D x ∂mu)) =
    ∫ x, rho x*g.inner x (G x) (G x) ∂mu
  ring

/-- Full completed H¹ image of every genuine weak observable, with its
original weighted mass and Dirichlet energy exactly preserved by gauge. -/
theorem half_density_weak_exists_completion_mass_energy (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n))))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))) :
    ∃ U : H1Compl (roundMetric (E := E) (n := n)),
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
        (fun x => DFLPhysicalHalfDensity.halfFactor p r x*u x) ∧
      ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2=
        ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(u x)^2
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) ∧
      potentialEnergy (roundMetric (E := E) (n := n))
        (DFLPhysicalHalfDensity.physicalPotential (n := n) p r) U=
        ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(roundMetric (E := E) (n := n)).inner x (G x) (G x)
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let h := DFLPhysicalHalfDensity.halfFactor p r
  obtain ⟨hhu,hhG,hhGn⟩ := hG.smooth_mul_witness (by norm_num : (1 : ℝ≥0∞)≤2) hu hGn
    (DFLPhysicalHalfDensity.halfFactor_smooth (n := n) p r)
  obtain ⟨U,hU,hUE⟩ := weakH1_function_exists_completion_energy g (fun x => h x*u x) hhu
    (halfDensityWeakGradient p r u G) hhG hhGn
  refine ⟨U,hU,?_,?_⟩
  · rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx]
    simp only [RCLike.inner_apply,conj_trivial]
    change (h x*u x)*(h x*u x)=_
    rw [← pow_two,mul_pow,DFLPhysicalHalfDensity.halfFactor_square]
  · unfold potentialEnergy
    rw [hUE]
    have hpot : (∫ x, DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(H1ComplToLp g U x)^2 ∂mu)=
        ∫ x, DFLPhysicalHalfDensity.physicalPotential (n := n) p r x*(h x*u x)^2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [hU] with x hx
      rw [hx]
    rw [hpot]
    exact half_density_weak_integral_energy p hp r u G hu hG hGn

end DFLWeakHalfDensity
