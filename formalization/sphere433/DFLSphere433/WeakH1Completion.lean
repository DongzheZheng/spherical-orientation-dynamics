import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakSmoothDensity
import Mathlib.Topology.MetricSpace.Sequences

/-! Identification of the actual smooth H1 completion with distributional
weak H1. The gradient witness is an arbitrary L2 tangent field, not a
smooth field supplied as a premise. -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLWeakH1Completion
open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

abbrev ScalarLp (g : SmoothRiemannianMetric I M) := Lp ℝ 2 (riemannianVolumeMeasure I M g)

def metricNorm (g : SmoothRiemannianMetric I M) (V : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  Real.sqrt (g.inner x (V x) (V x))

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem inner_self_nonneg (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem metricNorm_sub_triangle (g : SmoothRiemannianMetric I M) (x : M)
    (v w z : TangentSpace I x) :
    Real.sqrt (g.inner x (v - w) (v - w)) ≤
      Real.sqrt (g.inner x (v - z) (v - z)) + Real.sqrt (g.inner x (w - z) (w - z)) := by
  have hneg : Real.sqrt (g.inner x (-(w - z)) (-(w - z))) =
      Real.sqrt (g.inner x (w - z) (w - z)) := by
    have he : -(w - z) = (-1 : ℝ) • (w - z) := by simp
    rw [he, Geometry.Riemannian.sqrt_inner_smul]
    norm_num
  have h := Geometry.Riemannian.sqrt_inner_add_le g x (v - z) (-(w - z))
  have he : v - z + -(w - z) = v - w := by abel
  rwa [he, hneg] at h

omit [I.Boundaryless] in
theorem realLp_norm_sq (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : MemLp f 2 (riemannianVolumeMeasure I M g)) :
    (eLpNorm f 2 (riemannianVolumeMeasure I M g)).toReal ^ 2 =
      ∫ x, f x * f x ∂riemannianVolumeMeasure I M g := by
  let t := hf.toLp f
  have h := real_inner_self_eq_norm_sq t
  rw [L2.inner_def] at h
  rw [Lp.norm_toLp] at h
  rw [integral_congr_ae (by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx])] at h
  exact h.symm

theorem smoothMetricGrad_memLp (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    MemLp (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g) :=
  (Analysis.Sobolev.Equivalence.continuous_g_norm_gradFun g f.smooth).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem smooth_norm_sq (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    ‖f‖ ^ 2 = (eLpNorm f.toFun 2 (riemannianVolumeMeasure I M g)).toReal ^ 2 +
      (eLpNorm (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g)).toReal ^ 2 := by
  rw [realLp_norm_sq g f.toFun f.memLp_two,
    realLp_norm_sq g _ (smoothMetricGrad_memLp g f), f.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner metricNorm
  simp_rw [← sq, Real.sq_sqrt (inner_self_nonneg g _ _)]
  rfl

theorem smooth_grad_eLpNorm_le (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    eLpNorm (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g) ≤
      ENNReal.ofReal ‖f‖ := by
  rw [ENNReal.le_ofReal_iff_toReal_le (smoothMetricGrad_memLp g f).eLpNorm_ne_top (norm_nonneg f)]
  nlinarith [smooth_norm_sq g f, ENNReal.toReal_nonneg
    (a := eLpNorm (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g)),
    norm_nonneg f]

theorem smooth_norm_le_scalar_add_gradient (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    ‖f‖ ≤ (eLpNorm f.toFun 2 (riemannianVolumeMeasure I M g)).toReal +
      (eLpNorm (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g)).toReal := by
  nlinarith [smooth_norm_sq g f, ENNReal.toReal_nonneg
    (a := eLpNorm f.toFun 2 (riemannianVolumeMeasure I M g)), ENNReal.toReal_nonneg
    (a := eLpNorm (metricNorm g (gradFun g f.toFun)) 2 (riemannianVolumeMeasure I M g)),
    norm_nonneg f]

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem smooth_grad_sub (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) (x : M) :
    gradFun g (f - h).toFun x = gradFun g f.toFun x - gradFun g h.toFun x := by
  exact Geometry.Connection.gradFun_sub g
    (f.smooth.mdifferentiable (by simp) x) (h.smooth.mdifferentiable (by simp) x)


/-- A smooth sequence approaching any actual completion vector at a
geometric rate. The sequence is constructed by the proved dense range. -/
theorem exists_fast_smooth_approx (g : SmoothRiemannianMetric I M) (u : H1Compl g) :
    ∃ f : ℕ → SmoothScalar g,
      (∀ n, dist (smoothToH1Compl g (f n)) u ≤ (2 : ℝ)⁻¹ ^ n) ∧
      Tendsto (fun n => smoothToH1Compl g (f n)) atTop (𝓝 u) := by
  have hex (n : ℕ) : ∃ f : SmoothScalar g,
      dist (smoothToH1Compl g f) u < (2 : ℝ)⁻¹ ^ n := by
    obtain ⟨v, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.mp
      (denseRange_smoothToH1Compl g u) ((2 : ℝ)⁻¹ ^ n) (by positivity)
    exact ⟨f, by simpa only [dist_comm] using hf⟩
  choose f hf using hex
  refine ⟨f, fun n => (hf n).le, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
    (fun _ => dist_nonneg) (fun n => (hf n).le)

theorem smooth_h1_dist_eq (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ‖f - h‖ = dist (smoothToH1Compl g f) (smoothToH1Compl g h) := by
  rw [dist_eq_norm, ← map_sub, smoothToH1Compl_apply, UniformSpace.Completion.norm_coe]

theorem scalar_error_eq_edist (g : SmoothRiemannianMetric I M) (f : SmoothScalar g)
    (u : ScalarLp g) :
    eLpNorm (fun x => f.toFun x - u x) 2 (riemannianVolumeMeasure I M g) =
      edist (smoothToLp g f) u := by
  rw [Lp.edist_def]
  apply eLpNorm_congr_ae
  filter_upwards [f.memLp_two.coeFn_toLp] with x hx
  simp only [Pi.sub_apply]
  change f.toFun x - u x = (f.memLp_two.toLp f.toFun : M → ℝ) x - u x
  rw [hx]

/-- Every vector of the actual smooth `H¹` completion has a genuine
`L²` distributional Riemannian gradient. -/
theorem H1ComplToLp_exists_weak_gradient_energy (g : SmoothRiemannianMetric I M) (u : H1Compl g) :
    ∃ G : ∀ x : M, TangentSpace I x,
      HasWeakRiemannianGradLp g (H1ComplToLp g u : M → ℝ) G ∧
      MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g) ∧
      ‖u‖ ^ 2 - ‖H1ComplToLp g u‖ ^ 2 =
        ∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g := by
  classical
  obtain ⟨f, hf, htend⟩ := exists_fast_smooth_approx g u
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n
  let D : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ n
  have hδmono : Antitone δ := fun _ _ h =>
    pow_le_pow_of_le_one (by positivity) (by norm_num) h
  have hδD (n : ℕ) : ENNReal.ofReal (δ n) = D n := by
    simp [δ, D, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, inv_pow, ENNReal.inv_pow]
  let V (n : ℕ) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradG g ⟨(f n).toFun, (f n).smooth⟩
  have hV (n : ℕ) (x : M) : V n x = gradFun g (f n).toFun x := grad_g_apply _ _ _
  let d (n m : ℕ) := eLpNorm (fun x => Real.sqrt
    (g.inner x (V n x - V m x) (V n x - V m x))) 2 (riemannianVolumeMeasure I M g)
  have hd (n m : ℕ) : d n m ≤ D n + D m := by
    have heq : (fun x => Real.sqrt (g.inner x (V n x - V m x) (V n x - V m x))) =
        metricNorm g (gradFun g (f n - f m).toFun) := by
      funext x
      unfold metricNorm
      rw [hV, hV, smooth_grad_sub]
    dsimp only [d]
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal ‖f n - f m‖ := smooth_grad_eLpNorm_le g _
      _ ≤ ENNReal.ofReal (δ n + δ m) := by
        apply ENNReal.ofReal_le_ofReal
        rw [smooth_h1_dist_eq]
        exact (dist_triangle _ u _).trans (add_le_add (hf n) (by simpa only [δ, dist_comm] using hf m))
      _ = D n + D m := by rw [ENNReal.ofReal_add (by positivity) (by positivity), hδD, hδD]
  have hdmeas (n m : ℕ) : AEStronglyMeasurable (fun x => Real.sqrt
      (g.inner x (V n x - V m x) (V n x - V m x))) (riemannianVolumeMeasure I M g) :=
    (Real.continuous_sqrt.comp
      (TangentBundle.continuous_g_inner_of_smooth_sections g (V n - V m) (V n - V m))).aestronglyMeasurable
  let r : ℕ → ℝ≥0∞ := fun n => 2 * D n
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r, mul_zero] using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hDmono : Antitone D := fun _ _ h => pow_le_pow_of_le_one (by positivity) (by norm_num) h
  have hstep (n : ℕ) : d (n + 1) n ≤ r n := by
    exact (hd _ _).trans (by dsimp only [r]; rw [two_mul]; exact add_le_add (hDmono (Nat.le_succ n)) le_rfl)
  have hsum : (∑' n, d (n + 1) n) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hstep)
    dsimp only [r, D]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    norm_num
  have htail (n : ℕ) : ∀ᶠ m in atTop, d n m ≤ r n := by
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hd _ _).trans (by dsimp only [r]; rw [two_mul]; exact add_le_add le_rfl (hDmono hm))
  obtain ⟨G, hpoint, hmetric⟩ := exists_metricL2_limit_of_summable_steps g (fun n x => V n x)
    hdmeas hsum hr htail
  have hscalar : Tendsto (fun n => eLpNorm (fun x => (f n).toFun x - (H1ComplToLp g u) x)
      2 (riemannianVolumeMeasure I M g)) atTop (𝓝 0) := by
    have hJ := ((H1ComplToLp g).continuous.tendsto u).comp htend
    have hdist := hJ.edist (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => H1ComplToLp g u) atTop (𝓝 (H1ComplToLp g u)))
    simpa only [Function.comp_def, edist_self, H1ComplToLp_smoothToH1Compl, ← scalar_error_eq_edist] using hdist
  have hweak (n : ℕ) : HasWeakRiemannianGradLp g (f n).toFun (fun x => V n x) := by
    simpa only [hV] using Analysis.Sobolev.Equivalence.hasWeakRiemannianGradLp_gradFun g (f n).smooth
  refine ⟨G,
    HasWeakRiemannianGradLp.of_metricL2_limit V (fun n => (f n).memLp_two) (Lp.memLp _)
      hweak hpoint hscalar hmetric,
    memLp_metric_norm_of_smooth_limit g V hpoint hmetric, ?_⟩
  have hJ := ((H1ComplToLp g).continuous.tendsto u).comp htend
  have hnorm (n : ℕ) :
      ‖smoothToH1Compl g (f n)‖ ^ 2 - ‖H1ComplToLp g (smoothToH1Compl g (f n))‖ ^ 2 =
        ∫ x, g.inner x (V n x) (V n x) ∂riemannianVolumeMeasure I M g := by
    rw [H1ComplToLp_smoothToH1Compl, smoothToH1Compl_apply, UniformSpace.Completion.norm_coe,
      (f n).norm_sq_eq_inner_self]
    change smoothScalarH1Inner (f n) (f n) - ‖smoothToLpLin g (f n)‖ ^ 2 = _
    rw [(f n).norm_smoothToLp_sq]
    unfold smoothScalarH1Inner
    change (∫ x, (f n).toFun x * (f n).toFun x ∂riemannianVolumeMeasure I M g) +
      (∫ x, g.inner x (V n x) (V n x) ∂riemannianVolumeMeasure I M g) -
      (∫ x, (f n).toFun x * (f n).toFun x ∂riemannianVolumeMeasure I M g) = _
    ring
  have hEnergy : Tendsto (fun n => ∫ x, g.inner x (V n x) (V n x)
      ∂riemannianVolumeMeasure I M g) atTop (𝓝 (‖u‖ ^ 2 - ‖H1ComplToLp g u‖ ^ 2)) := by
    convert (htend.norm.pow 2).sub (hJ.norm.pow 2) using 1
    funext n
    exact (hnorm n).symm
  exact tendsto_nhds_unique hEnergy
    (tendsto_integral_metric_energy_of_smooth_limit g V hpoint hmetric)

/-- Membership in the actual smooth completion implies distributional weak H1. -/
theorem H1ComplToLp_memW1pIntrinsicLp (g : SmoothRiemannianMetric I M) (u : H1Compl g) :
    MemW1pIntrinsicLp g 2 (H1ComplToLp g u : M → ℝ) := by
  obtain ⟨G, hG, hGn, _⟩ := H1ComplToLp_exists_weak_gradient_energy g u
  exact ⟨Lp.memLp _, G, hG, hGn⟩


/-- The gradient error of a smooth approximating sequence is measurable
and square integrable. Measurability follows from its actual a.e. tangent
field limit, not from a smoothness assumption on the weak gradient. -/
theorem metric_error_memLp (g : SmoothRiemannianMetric I M)
    (f : ℕ → SmoothScalar g) {G : ∀ x : M, TangentSpace I x}
    (hG : MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g))
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      Tendsto (fun n => gradFun g (f n).toFun x) atTop (𝓝 (G x))) (n : ℕ) :
    MemLp (metricNorm g (fun x => gradFun g (f n).toFun x - G x)) 2
      (riemannianVolumeMeasure I M g) := by
  have has : AEStronglyMeasurable
      (metricNorm g (fun x => gradFun g (f n).toFun x - G x))
      (riemannianVolumeMeasure I M g) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun j =>
      (smoothMetricGrad_memLp g (f n - f j)).aestronglyMeasurable)
    filter_upwards [hpoint] with x hx
    have hc : Continuous (fun v : TangentSpace I x => Real.sqrt
        (g.inner x (gradFun g (f n).toFun x - v) (gradFun g (f n).toFun x - v))) :=
      Real.continuous_sqrt.comp
        (((g.inner x).continuous.comp (continuous_const.sub continuous_id)).clm_apply
          (continuous_const.sub continuous_id))
    simpa only [Function.comp_def, metricNorm, smooth_grad_sub] using (hc.tendsto (G x)).comp hx
  apply MemLp.of_le ((smoothMetricGrad_memLp g (f n)).add hG) has
  filter_upwards with x
  have h := metricNorm_sub_triangle g x (gradFun g (f n).toFun x) (G x) 0
  simpa only [metricNorm, sub_zero, Real.norm_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply,
    Real.norm_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using h

/-- Smooth approximation in value and metric gradient is Cauchy in the
source's actual H1 norm. -/
theorem smooth_cauchy_of_metricL2_approx (g : SmoothRiemannianMetric I M)
    (u : ScalarLp g) (f : ℕ → SmoothScalar g) {G : ∀ x : M, TangentSpace I x}
    (hG : MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g))
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      Tendsto (fun n => gradFun g (f n).toFun x) atTop (𝓝 (G x)))
    (hscalar : Tendsto (fun n => eLpNorm (fun x => (f n).toFun x - u x) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0))
    (hmetric : Tendsto (fun n => eLpNorm
      (metricNorm g (fun x => gradFun g (f n).toFun x - G x)) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) : CauchySeq f := by
  let μ := riemannianVolumeMeasure I M g
  let A (n : ℕ) := eLpNorm (fun x => (f n).toFun x - u x) 2 μ
  let B (n : ℕ) := eLpNorm (metricNorm g (fun x => gradFun g (f n).toFun x - G x)) 2 μ
  have hmA (n : ℕ) : MemLp (fun x => (f n).toFun x - u x) 2 μ :=
    (f n).memLp_two.sub (Lp.memLp u)
  have hmB (n : ℕ) := metric_error_memLp g f hG hpoint n
  have hscalarSub (n m : ℕ) : eLpNorm (f n - f m).toFun 2 μ ≤ A n + A m := by
    have heq : (f n - f m).toFun =
        (fun x => (f n).toFun x - u x) - (fun x => (f m).toFun x - u x) := by
      funext x
      change (f n).toFun x - (f m).toFun x = _
      simp
    rw [heq]
    exact eLpNorm_sub_le (hmA n).aestronglyMeasurable (hmA m).aestronglyMeasurable (by norm_num)
  have hmetricSub (n m : ℕ) :
      eLpNorm (metricNorm g (gradFun g (f n - f m).toFun)) 2 μ ≤ B n + B m := by
    apply (eLpNorm_mono_ae (μ := μ) (p := 2) (f := metricNorm g (gradFun g (f n - f m).toFun))
      (g := metricNorm g (fun x => gradFun g (f n).toFun x - G x) +
        metricNorm g (fun x => gradFun g (f m).toFun x - G x)) ?_).trans
    · exact eLpNorm_add_le (hmB n).aestronglyMeasurable (hmB m).aestronglyMeasurable (by norm_num)
    · filter_upwards with x
      simp only [metricNorm, smooth_grad_sub, Pi.add_apply,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      exact metricNorm_sub_triangle g x _ _ _
  have hnorm (n m : ℕ) : ‖f n - f m‖ ≤ (A n).toReal + (A m).toReal + (B n).toReal + (B m).toReal := by
    have hA := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨(hmA n).eLpNorm_ne_top, (hmA m).eLpNorm_ne_top⟩) (hscalarSub n m)
    have hB := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨(hmB n).eLpNorm_ne_top, (hmB m).eLpNorm_ne_top⟩) (hmetricSub n m)
    rw [ENNReal.toReal_add (hmA n).eLpNorm_ne_top (hmA m).eLpNorm_ne_top] at hA
    rw [ENNReal.toReal_add (hmB n).eLpNorm_ne_top (hmB m).eLpNorm_ne_top] at hB
    have hn := smooth_norm_le_scalar_add_gradient g (f n - f m)
    linarith
  have hA : Tendsto (fun n => (A n).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, A, μ, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hscalar
  have hB : Tendsto (fun n => (B n).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, B, μ, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hmetric
  have hAB : Tendsto (fun n => (A n).toReal + (B n).toReal) atTop (𝓝 0) := by
    simpa only [add_zero] using hA.add hB
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hAB.eventually (Iio_mem_nhds hε₂))
  refine ⟨N, fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  have hn' := hN n hn
  have hm' := hN m hm
  exact (hnorm n m).trans_lt (by linarith)

/-- Every actual distributional weak H1 class comes from the smooth H1
completion. No smoothness of its weak tangent gradient is assumed. -/
theorem memW1pIntrinsicLp_exists_H1Compl [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u : ScalarLp g)
    (hu : MemW1pIntrinsicLp g 2 (u : M → ℝ)) :
    ∃ U : H1Compl g, H1ComplToLp g U = u := by
  classical
  obtain ⟨_, G, hG, hGn⟩ := hu
  obtain ⟨f₀, hf₀, hscalar, hpoint, hmetric⟩ :=
    hG.exists_smooth_metricL2_approx (Lp.memLp u) hGn
  let f : ℕ → SmoothScalar g := fun n => ⟨f₀ n, hf₀ n⟩
  have hC : CauchySeq f := smooth_cauchy_of_metricL2_approx g u f hGn hpoint hscalar hmetric
  have hC' : CauchySeq (fun n => smoothToH1Compl g (f n)) :=
    (smoothToH1Compl g).uniformContinuous.comp_cauchySeq hC
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete hC'
  refine ⟨U, ?_⟩
  have hJ := ((H1ComplToLp g).continuous.tendsto U).comp hU
  have hLp : Tendsto (fun n => smoothToLp g (f n)) atTop (𝓝 u) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hscalar
    change Tendsto (fun n => (eLpNorm (fun x => (f n).toFun x - u x) 2
      (riemannianVolumeMeasure I M g)).toReal) atTop (𝓝 (ENNReal.toReal 0)) at h
    simpa only [ENNReal.toReal_zero, scalar_error_eq_edist, edist_dist,
      ENNReal.toReal_ofReal (dist_nonneg)] using h
  have hJ' : Tendsto (fun n => smoothToLp g (f n)) atTop (𝓝 (H1ComplToLp g U)) := by
    simpa only [Function.comp_def, H1ComplToLp_smoothToH1Compl] using hJ
  exact tendsto_nhds_unique hJ' hLp

/-- Equality of domains between the actual source smooth H1 completion
and the conventional distributional weak-gradient H1 classes. -/
theorem H1ComplToLp_range_eq_weakH1 [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) :
    Set.range (H1ComplToLp g) = {u : ScalarLp g | MemW1pIntrinsicLp g 2 (u : M → ℝ)} := by
  ext u
  constructor
  · rintro ⟨U, rfl⟩
    exact H1ComplToLp_memW1pIntrinsicLp g U
  · intro hu
    exact memW1pIntrinsicLp_exists_H1Compl g u hu


/-- The energy identity holds for every given L2 distributional gradient,
by the proved a.e. uniqueness of weak Riemannian gradients. -/
theorem H1ComplToLp_weak_gradient_energy (g : SmoothRiemannianMetric I M)
    (U : H1Compl g) (G : ∀ x : M, TangentSpace I x)
    (hweak : HasWeakRiemannianGradLp g (H1ComplToLp g U : M → ℝ) G)
    (hGn : MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g)) :
    ‖U‖ ^ 2 - ‖H1ComplToLp g U‖ ^ 2 =
      ∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g := by
  obtain ⟨G₀, hw₀, hn₀, he₀⟩ := H1ComplToLp_exists_weak_gradient_energy g U
  have heq : G₀ =ᵐ[riemannianVolumeMeasure I M g] G := hw₀.ae_eq hweak
    (hn₀.mono_exponent (by norm_num)) (hGn.mono_exponent (by norm_num))
  rw [he₀]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

/-- A weak H1 class and its given gradient enter the actual smooth
completion with exactly the same value and Dirichlet energy. -/
theorem weakH1_exists_completion_energy [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u : ScalarLp g)
    (G : ∀ x : M, TangentSpace I x)
    (hweak : HasWeakRiemannianGradLp g (u : M → ℝ) G)
    (hGn : MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g)) :
    ∃ U : H1Compl g, H1ComplToLp g U = u ∧
      ‖U‖ ^ 2 - ‖u‖ ^ 2 = ∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g := by
  obtain ⟨U, hU⟩ := memW1pIntrinsicLp_exists_H1Compl g u ⟨Lp.memLp _, G, hweak, hGn⟩
  refine ⟨U, hU, ?_⟩
  have hw : HasWeakRiemannianGradLp g (H1ComplToLp g U : M → ℝ) G := by
    simpa only [hU] using hweak
  simpa only [hU] using H1ComplToLp_weak_gradient_energy g U G hw hGn

/-- Representative version for an arbitrary weak H1 function. -/
theorem weakH1_function_exists_completion_energy [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ)
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (G : ∀ x : M, TangentSpace I x)
    (hweak : HasWeakRiemannianGradLp g u G)
    (hGn : MemLp (metricNorm g G) 2 (riemannianVolumeMeasure I M g)) :
    ∃ U : H1Compl g,
      (H1ComplToLp g U : M → ℝ) =ᵐ[riemannianVolumeMeasure I M g] u ∧
      ‖U‖ ^ 2 - ‖H1ComplToLp g U‖ ^ 2 =
        ∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g := by
  let uLp : ScalarLp g := hu.toLp u
  have hw : HasWeakRiemannianGradLp g (uLp : M → ℝ) G :=
    hweak.congr_fun_ae hu.coeFn_toLp.symm
  obtain ⟨U, hU, hE⟩ := weakH1_exists_completion_energy g uLp G hw hGn
  exact ⟨U, hU ▸ hu.coeFn_toLp, by simpa only [hU] using hE⟩

end DFLWeakH1Completion
