import DFLSphere433.RoundSphereSharpGap
import DFLSphere433.WeakH1Completion

/-! Poincaré coercivity for the original full weak H¹ domain with the
von Mises--Fisher density exp(r t). Normalizing the density cancels from
both sides. The bound uses its exact maximum/minimum ratio exp(2 |r|). -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere
open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DFLWeakH1Completion

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩

abbrev roundBaseVolume (k : ℕ) :=
  riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)

private local instance (k : ℕ) : IsFiniteMeasure (roundBaseVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- The sharp sphere estimate on arbitrary distributional weak H¹ functions. -/
theorem roundWeakH1_poincare (k : ℕ) (f : RoundSphere k → ℝ)
    (hf : MemLp f 2 (roundBaseVolume k))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k + 2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k) f G)
    (hGn : MemLp (metricNorm (roundSphereMetric k) G) 2 (roundBaseVolume k))
    (hmean : (∫ x, f x ∂roundBaseVolume k) = 0) :
    (k + 2 : ℝ) * (∫ x, f x ^ 2 ∂roundBaseVolume k) ≤
      ∫ x, (roundSphereMetric k).inner x (G x) (G x) ∂roundBaseVolume k := by
  obtain ⟨U, hU, hE⟩ := weakH1_function_exists_completion_energy
    (roundSphereMetric k) f hf G hG hGn
  have hm : (∫ x, (H1ComplToLp (roundSphereMetric k) U) x ∂roundBaseVolume k) = 0 :=
    (integral_congr_ae hU).trans hmean
  have hn : ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2 =
      ∫ x, f x ^ 2 ∂roundBaseVolume k := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx, Real.inner_apply, pow_two]
  have h := roundSphere_h1_poincare k U hm
  rw [hE, hn] at h
  exact h

/-- Subtracting a constant preserves the given distributional gradient. -/
theorem weak_gradient_sub_const (k : ℕ) (f : RoundSphere k → ℝ)
    (hf : MemLp f 2 (roundBaseVolume k))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k + 2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k) f G)
    (hGn : MemLp (metricNorm (roundSphereMetric k) G) 2 (roundBaseVolume k)) (c : ℝ) :
    HasWeakRiemannianGradLp (roundSphereMetric k) (fun x => f x - c) G := by
  have hc : HasWeakRiemannianGradLp (roundSphereMetric k) (fun _ : RoundSphere k => -c)
      (fun _ => 0) := by
    have h := Analysis.Sobolev.Equivalence.hasWeakRiemannianGradLp_gradFun
      (roundSphereMetric k) (contMDiff_const :
        ContMDiff (𝓡 (k + 2)) 𝓘(ℝ, ℝ) ∞ (fun _ : RoundSphere k => -c))
    exact hasWeakRiemannianGradLp_congr_ae (ae_of_all _ (fun _ => rfl))
      (ae_of_all _ (fun x => Geometry.Connection.gradFun_const _ _ x)) h
  have hzero : MemLp (metricNorm (roundSphereMetric k) (fun _ => 0)) 2 (roundBaseVolume k) := by
    have hz : metricNorm (roundSphereMetric k) (fun _ => 0) =
        (fun _ : RoundSphere k => (0 : ℝ)) := by
      funext x
      change Real.sqrt ((roundSphereMetric k).inner x 0 0) = 0
      rw [map_zero, Real.sqrt_zero]
    rw [hz]
    exact MemLp.zero
  have h := hG.add (p := 2) (by norm_num) hc hf (memLp_const (-c)) hGn hzero
  exact hasWeakRiemannianGradLp_congr_ae
    (ae_of_all _ (fun x => by simp only [sub_eq_add_neg]))
    (ae_of_all _ (fun x => add_zero (G x))) h

/-- Full weak H¹ Poincaré after centering in the unweighted volume. -/
theorem roundWeakH1_centered_poincare (k : ℕ) (f : RoundSphere k → ℝ)
    (hf : MemLp f 2 (roundBaseVolume k))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k + 2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k) f G)
    (hGn : MemLp (metricNorm (roundSphereMetric k) G) 2 (roundBaseVolume k)) :
    ∃ c : ℝ, (k + 2 : ℝ) * (∫ x, (f x - c) ^ 2 ∂roundBaseVolume k) ≤
      ∫ x, (roundSphereMetric k).inner x (G x) (G x) ∂roundBaseVolume k := by
  let μ := roundBaseVolume k
  let c := (∫ x, f x ∂μ) / μ.real Set.univ
  have hnonempty : Nonempty (RoundSphere k) := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  let : Nonempty (RoundSphere k) := hnonempty
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (roundSphereMetric k)
  have hvol : μ.real Set.univ ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩
  have hfc : MemLp (fun x => f x - c) 2 μ := hf.sub (memLp_const c)
  have hmean : (∫ x, (f x - c) ∂μ) = 0 := by
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const c), integral_const]
    dsimp only [c]
    rw [smul_eq_mul]
    change (∫ x, f x ∂μ) - μ.real Set.univ * ((∫ x, f x ∂μ) / μ.real Set.univ) = 0
    field_simp
    ring
  exact ⟨c, roundWeakH1_poincare k _ hfc G (weak_gradient_sub_const k f hf G hG hGn c) hGn hmean⟩

/-- A weighted mean-zero function has no larger second moment than its
second moment about any other constant. -/
theorem weighted_second_moment_le_centered {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w f : X → ℝ) (c : ℝ)
    (hw : Integrable w μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hwf2 : Integrable (fun x => w x * f x ^ 2) μ)
    (hwpos : ∀ x, 0 ≤ w x) (hmean : (∫ x, w x * f x ∂μ) = 0) :
    (∫ x, w x * f x ^ 2 ∂μ) ≤ ∫ x, w x * (f x - c) ^ 2 ∂μ := by
  have hid : (fun x => w x * (f x - c) ^ 2) =
      (fun x => w x * f x ^ 2 - (2 * c) * (w x * f x) + c ^ 2 * w x) := by
    funext x
    ring
  have hsum : (∫ x, w x * f x ^ 2 - (2 * c) * (w x * f x) + c ^ 2 * w x ∂μ) =
      (∫ x, w x * f x ^ 2 ∂μ) - (2 * c) * (∫ x, w x * f x ∂μ) + c ^ 2 * ∫ x, w x ∂μ := by
    calc
      _ = (∫ x, w x * f x ^ 2 - (2 * c) * (w x * f x) ∂μ) +
          ∫ x, c ^ 2 * w x ∂μ := integral_add (hwf2.sub (hwf.const_mul _)) (hw.const_mul _)
      _ = _ := by rw [integral_sub hwf2 (hwf.const_mul _), integral_const_mul, integral_const_mul]
  rw [hid, hsum, hmean]
  have hnonneg : 0 ≤ c ^ 2 * ∫ x, w x ∂μ :=
    mul_nonneg (sq_nonneg c) (integral_nonneg hwpos)
  linarith

/-- The actual unnormalized vMF density on the original round sphere. -/
def vMFWeight (k : ℕ) (r : ℝ) (x : RoundSphere k) : ℝ :=
  Real.exp (r * (roundCoordinate k).toFun x)

theorem vMFWeight_continuous (k : ℕ) (r : ℝ) : Continuous (vMFWeight k r) :=
  Real.continuous_exp.comp (continuous_const.mul (roundCoordinate k).smooth.continuous)

theorem roundCoordinate_abs_le_one (k : ℕ) (x : RoundSphere k) :
    |(roundCoordinate k).toFun x| ≤ 1 := by
  change |⟪EuclideanSpace.single 0 1, (x : RoundAmbient k)⟫_ℝ| ≤ 1
  calc
    _ ≤ ‖EuclideanSpace.single 0 1‖ * ‖(x : RoundAmbient k)‖ := abs_real_inner_le_norm _ _
    _ = 1 := by rw [norm_eq_of_mem_sphere x]; simp

theorem vMFWeight_bounds (k : ℕ) (r : ℝ) (x : RoundSphere k) :
    Real.exp (-|r|) ≤ vMFWeight k r x ∧ vMFWeight k r x ≤ Real.exp |r| := by
  have habs : |r * (roundCoordinate k).toFun x| ≤ |r| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (roundCoordinate_abs_le_one k x) (abs_nonneg r)
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp habs).1, Real.exp_le_exp.mpr (abs_le.mp habs).2⟩

/-- The physical unnormalized vMF measure; its normalization cancels in
all Rayleigh quotients and Poincaré estimates. -/
def vMFVolume (k : ℕ) (r : ℝ) : Measure (RoundSphere k) :=
  (roundBaseVolume k).withDensity (fun x => ENNReal.ofReal (vMFWeight k r x))

theorem vMFVolume_comparison (k : ℕ) (r : ℝ) :
    vMFVolume k r ≤ ENNReal.ofReal (Real.exp |r|) • roundBaseVolume k ∧
      roundBaseVolume k ≤ ENNReal.ofReal (Real.exp |r|) • vMFVolume k r := by
  have hu : vMFVolume k r ≤ ENNReal.ofReal (Real.exp |r|) • roundBaseVolume k := by
    have h := withDensity_mono (μ := roundBaseVolume k)
      (ae_of_all _ (fun x => ENNReal.ofReal_le_ofReal (vMFWeight_bounds k r x).2))
    simpa only [vMFVolume, withDensity_const] using h
  have hl : ENNReal.ofReal (Real.exp (-|r|)) • roundBaseVolume k ≤ vMFVolume k r := by
    have h := withDensity_mono (μ := roundBaseVolume k)
      (ae_of_all _ (fun x => ENNReal.ofReal_le_ofReal (vMFWeight_bounds k r x).1))
    simpa only [vMFVolume, withDensity_const] using h
  have hinv : ENNReal.ofReal (Real.exp |r|) * ENNReal.ofReal (Real.exp (-|r|)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp
  refine ⟨hu, ?_⟩
  calc
    roundBaseVolume k = ENNReal.ofReal (Real.exp |r|) •
        (ENNReal.ofReal (Real.exp (-|r|)) • roundBaseVolume k) := by rw [smul_smul, hinv, one_smul]
    _ ≤ _ := _root_.smul_le_smul_left _ hl

/-- The weighted and unweighted L² requirements have exactly the same
domain, including for the norm of a distributional weak gradient. -/
theorem vMF_memLp_iff (k : ℕ) (r : ℝ) (f : RoundSphere k → ℝ) :
    MemLp f 2 (vMFVolume k r) ↔ MemLp f 2 (roundBaseVolume k) := by
  constructor
  · exact fun hf => hf.of_measure_le_smul ENNReal.ofReal_ne_top (vMFVolume_comparison k r).2
  · exact fun hf => hf.of_measure_le_smul ENNReal.ofReal_ne_top (vMFVolume_comparison k r).1

theorem vMFVolume_integral (k : ℕ) (r : ℝ) (f : RoundSphere k → ℝ) :
    (∫ x, f x ∂vMFVolume k r) = ∫ x, vMFWeight k r x * f x ∂roundBaseVolume k := by
  have hm : Measurable (fun x => ENNReal.ofReal (vMFWeight k r x)) :=
    ENNReal.measurable_ofReal.comp (vMFWeight_continuous k r).measurable
  have h := integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all (roundBaseVolume k) (fun _ => ENNReal.ofReal_lt_top)) f
  exact h.trans (integral_congr_ae (ae_of_all _ (fun x => by
    change (ENNReal.ofReal (vMFWeight k r x)).toReal • f x = vMFWeight k r x * f x
    rw [ENNReal.toReal_ofReal (show 0 ≤ vMFWeight k r x from (Real.exp_pos _).le), smul_eq_mul])))

/-- A genuine all-domain estimate for the original vMF weighted sphere.
The only function assumptions are its actual distributional weak H¹
membership and the physical weighted mean-zero constraint. -/
theorem vMFWeakH1_poincare (k : ℕ) (r : ℝ) (f : RoundSphere k → ℝ)
    (hf : MemLp f 2 (roundBaseVolume k))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k + 2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k) f G)
    (hGn : MemLp (metricNorm (roundSphereMetric k) G) 2 (roundBaseVolume k))
    (hmean : (∫ x, vMFWeight k r x * f x ∂roundBaseVolume k) = 0) :
    (k + 2 : ℝ) * Real.exp (-2 * |r|) *
      (∫ x, vMFWeight k r x * f x ^ 2 ∂roundBaseVolume k) ≤
      ∫ x, vMFWeight k r x * (roundSphereMetric k).inner x (G x) (G x) ∂roundBaseVolume k := by
  let μ := roundBaseVolume k
  let w := vMFWeight k r
  let E := fun x => (roundSphereMetric k).inner x (G x) (G x)
  have hwcont : Continuous w := vMFWeight_continuous k r
  have hwint : Integrable w μ := hwcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hwbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ Real.exp |r| := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    change |Real.exp (r * (roundCoordinate k).toFun x)| ≤ Real.exp |r|
    rw [Real.abs_exp]
    exact (vMFWeight_bounds k r x).2
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hf2int : Integrable (fun x => f x ^ 2) μ := by
    exact (hf.integrable_mul hf).congr (ae_of_all _ (fun x => by simp only [Pi.mul_apply, pow_two]))
  have hwf : Integrable (fun x => w x * f x) μ := hfint.bdd_mul hwcont.aestronglyMeasurable hwbound
  have hwf2 : Integrable (fun x => w x * f x ^ 2) μ := hf2int.bdd_mul hwcont.aestronglyMeasurable hwbound
  have hEpos : ∀ x, 0 ≤ E x := fun x => inner_self_nonneg (roundSphereMetric k) x (G x)
  have hEint : Integrable E μ := by
    have hid : (fun x => metricNorm (roundSphereMetric k) G x * metricNorm (roundSphereMetric k) G x) = E := by
      funext x
      change Real.sqrt (E x) * Real.sqrt (E x) = E x
      rw [← pow_two, Real.sq_sqrt (hEpos x)]
    have h := hGn.integrable_mul hGn
    change Integrable (fun x => metricNorm (roundSphereMetric k) G x * metricNorm (roundSphereMetric k) G x) μ at h
    rwa [hid] at h
  have hwEint : Integrable (fun x => w x * E x) μ := hEint.bdd_mul hwcont.aestronglyMeasurable hwbound
  obtain ⟨c, hcenter⟩ := roundWeakH1_centered_poincare k f hf G hG hGn
  have hfc2int : Integrable (fun x => (f x - c) ^ 2) μ := by
    have hfc := hf.sub (memLp_const c)
    exact (hfc.integrable_mul hfc).congr
      (ae_of_all _ (fun x => by simp only [Pi.mul_apply, Pi.sub_apply, pow_two]))
  have hwfc2int : Integrable (fun x => w x * (f x - c) ^ 2) μ :=
    hfc2int.bdd_mul hwcont.aestronglyMeasurable hwbound
  have hvariance : (∫ x, w x * f x ^ 2 ∂μ) ≤
      ∫ x, w x * (f x - c) ^ 2 ∂μ :=
    weighted_second_moment_le_centered μ w f c hwint hwf hwf2
      (fun x => (Real.exp_pos _).le) hmean
  have hupper : (∫ x, w x * (f x - c) ^ 2 ∂μ) ≤
      Real.exp |r| * ∫ x, (f x - c) ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hwfc2int (hfc2int.const_mul _) (fun x =>
      mul_le_mul_of_nonneg_right (vMFWeight_bounds k r x).2 (sq_nonneg _))
  have hweighted : (k + 2 : ℝ) * (∫ x, w x * f x ^ 2 ∂μ) ≤
      Real.exp |r| * ∫ x, E x ∂μ := calc
    _ ≤ (k + 2 : ℝ) * (Real.exp |r| * ∫ x, (f x - c) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (hvariance.trans hupper) (by positivity)
    _ = Real.exp |r| * ((k + 2 : ℝ) * ∫ x, (f x - c) ^ 2 ∂μ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcenter (Real.exp_pos _).le
  have hlower : Real.exp (-|r|) * (∫ x, E x ∂μ) ≤ ∫ x, w x * E x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (hEint.const_mul _) hwEint (fun x =>
      mul_le_mul_of_nonneg_right (vMFWeight_bounds k r x).1 (hEpos x))
  have hinv : Real.exp (-|r|) * Real.exp |r| = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaled : Real.exp (-|r|) * ((k + 2 : ℝ) * ∫ x, w x * f x ^ 2 ∂μ) ≤ ∫ x, E x ∂μ := calc
    _ ≤ Real.exp (-|r|) * (Real.exp |r| * ∫ x, E x ∂μ) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, hinv, one_mul]
  have htwice : Real.exp (-|r|) * (Real.exp (-|r|) *
      ((k + 2 : ℝ) * ∫ x, w x * f x ^ 2 ∂μ)) ≤ ∫ x, w x * E x ∂μ :=
    (mul_le_mul_of_nonneg_left hscaled (Real.exp_pos _).le).trans hlower
  have hfactor : Real.exp (-2 * |r|) = Real.exp (-|r|) * Real.exp (-|r|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  convert htwice using 1
  ring

/-- The same estimate written directly with the original weighted
measure and weighted L² function/gradient domain. -/
theorem vMFWeightedH1_poincare (k : ℕ) (r : ℝ) (f : RoundSphere k → ℝ)
    (hf : MemLp f 2 (vMFVolume k r))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k + 2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k) f G)
    (hGn : MemLp (metricNorm (roundSphereMetric k) G) 2 (vMFVolume k r))
    (hmean : (∫ x, f x ∂vMFVolume k r) = 0) :
    (k + 2 : ℝ) * Real.exp (-2 * |r|) * (∫ x, f x ^ 2 ∂vMFVolume k r) ≤
      ∫ x, (roundSphereMetric k).inner x (G x) (G x) ∂vMFVolume k r := by
  rw [vMFVolume_integral] at hmean
  rw [vMFVolume_integral, vMFVolume_integral]
  exact vMFWeakH1_poincare k r f ((vMF_memLp_iff k r f).mp hf) G hG
    ((vMF_memLp_iff k r _).mp hGn) hmean

end DFLSphere

#print axioms DFLSphere.roundWeakH1_poincare
#print axioms DFLSphere.roundWeakH1_centered_poincare
#print axioms DFLSphere.vMFWeight_bounds

#print axioms DFLSphere.vMFWeakH1_poincare

#print axioms DFLSphere.vMF_memLp_iff
#print axioms DFLSphere.vMFWeightedH1_poincare
