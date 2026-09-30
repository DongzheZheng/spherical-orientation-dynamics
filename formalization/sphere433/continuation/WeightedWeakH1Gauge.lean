import continuation.WeakHalfDensityEnergy
import continuation.PhysicalGapFullDomain

/-! The actual vMF weighted distributional weak H¹ domain and its exact
half-density correspondence. All L² conditions use the original weighted
measure; weak gradients are the intrinsic distributional gradients of the
actual round geometry. Weight normalization cancels in the optimal rate. -/
noncomputable section
set_option maxHeartbeats 1600000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFLWeakH1Completion DFLWeakHalfDensity DFLPhysicalHalfDensity DFLCompactPotential
open DFLDriftBaseline DFLPhysicalGap
namespace DFLWeightedWeakH1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The original unnormalized exponential density against actual round
Riemannian volume, on the entire physical sphere. -/
def weightedSphereVolume (p : E) (r : ℝ) : Measure (sphere (0 : E) 1) :=
  (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))).withDensity
    (fun x => ENNReal.ofReal (Real.exp (r*⟪p,(x : E)⟫_ℝ)))

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+1)] in
theorem sphereWeight_bounds (p : E) (hp : ‖p‖=1) (r : ℝ) (x : sphere (0 : E) 1) :
    Real.exp (-|r|)≤Real.exp (r*⟪p,(x : E)⟫_ℝ) ∧
      Real.exp (r*⟪p,(x : E)⟫_ℝ)≤Real.exp |r| := by
  have ht : |⟪p,(x : E)⟫_ℝ|≤1 := by
    calc
      _ ≤ ‖p‖*‖(x : E)‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hp,norm_eq_of_mem_sphere x]; norm_num
  have habs : |r*⟪p,(x : E)⟫_ℝ|≤|r| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg r)
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp habs).1,Real.exp_le_exp.mpr (abs_le.mp habs).2⟩

theorem weightedSphereVolume_comparison (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedSphereVolume (n := n) p r ≤ ENNReal.ofReal (Real.exp |r|) •
      riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) ∧
    riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) ≤
      ENNReal.ofReal (Real.exp |r|) • weightedSphereVolume (n := n) p r := by
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))
  have hu : weightedSphereVolume (n := n) p r ≤ ENNReal.ofReal (Real.exp |r|) • mu := by
    have h := withDensity_mono (μ := mu)
      (ae_of_all _ (fun x => ENNReal.ofReal_le_ofReal (sphereWeight_bounds p hp r x).2))
    simpa only [weightedSphereVolume,withDensity_const] using h
  have hl : ENNReal.ofReal (Real.exp (-|r|)) • mu ≤ weightedSphereVolume (n := n) p r := by
    have h := withDensity_mono (μ := mu)
      (ae_of_all _ (fun x => ENNReal.ofReal_le_ofReal (sphereWeight_bounds p hp r x).1))
    simpa only [weightedSphereVolume,withDensity_const] using h
  have hinv : ENNReal.ofReal (Real.exp |r|)*ENNReal.ofReal (Real.exp (-|r|))=1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,add_neg_cancel,Real.exp_zero]
    simp
  refine ⟨hu,?_⟩
  calc
    mu = ENNReal.ofReal (Real.exp |r|) • (ENNReal.ofReal (Real.exp (-|r|)) • mu) := by
      rw [smul_smul,hinv,one_smul]
    _ ≤ _ := _root_.smul_le_smul_left _ hl

/-- The actual weighted and unweighted L² domains agree, for values and
for arbitrary metric norms of distributional weak tangent fields. -/
theorem weightedSphere_memLp_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) :
    MemLp f 2 (weightedSphereVolume (n := n) p r) ↔
    MemLp f 2 (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n))) := by
  constructor
  · exact fun hf => hf.of_measure_le_smul ENNReal.ofReal_ne_top (weightedSphereVolume_comparison p hp r).2
  · exact fun hf => hf.of_measure_le_smul ENNReal.ofReal_ne_top (weightedSphereVolume_comparison p hp r).1

theorem weightedSphereVolume_integral (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) :
    (∫ x, f x ∂weightedSphereVolume (n := n) p r)=
    ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  have hc : Continuous (fun x : sphere (0 : E) 1 => Real.exp (r*⟪p,(x : E)⟫_ℝ)) := by fun_prop
  have hm : Measurable (fun x : sphere (0 : E) 1 => ENNReal.ofReal (Real.exp (r*⟪p,(x : E)⟫_ℝ))) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  have h := integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))
      (fun _ => ENNReal.ofReal_lt_top)) f
  exact h.trans (integral_congr_ae (ae_of_all _ (fun x => by
    change (ENNReal.ofReal (Real.exp (r*⟪p,(x : E)⟫_ℝ))).toReal • f x=_
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul])))

/-- The conventional weighted weak H¹ domain: the value and genuine
distributional round gradient have finite weighted L² norm. -/
def WeightedWeakH1 (p : E) (r : ℝ) (u : sphere (0 : E) 1 → ℝ) : Prop :=
  MemLp u 2 (weightedSphereVolume (n := n) p r) ∧
    ∃ G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x,
      HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G ∧
      MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r)

/-- The original weighted weak domain equals the intrinsic distributional
weak H¹ domain, as expected from the bounded positive smooth density. -/
theorem weightedWeakH1_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) :
    WeightedWeakH1 (n := n) p r u ↔ MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2 u := by
  constructor
  · rintro ⟨hu,G,hG,hGn⟩
    exact ⟨(weightedSphere_memLp_iff p hp r u).mp hu,G,hG,
      (weightedSphere_memLp_iff p hp r _).mp hGn⟩
  · rintro ⟨hu,G,hG,hGn⟩
    exact ⟨(weightedSphere_memLp_iff p hp r u).mpr hu,G,hG,
      (weightedSphere_memLp_iff p hp r _).mpr hGn⟩

variable [NeZero n]
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

omit [NeZero n] in
/-- True two-way identification of the original weighted weak domain and
the half-density distributional weak H¹ domain. -/
theorem weightedWeakH1_half_density_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) :
    WeightedWeakH1 (n := n) p r u ↔ MemW1pIntrinsicLp (roundMetric (E := E) (n := n)) 2
      (fun x => halfFactor p r x*u x) := by
  rw [weightedWeakH1_iff p hp r u,half_density_weakH1_iff p r u]

/-- Exact equality of domains with the genuine full H¹ completion, using
actual a.e. representatives rather than a smooth-core restriction. -/
theorem weightedWeakH1_completion_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) :
    WeightedWeakH1 (n := n) p r u ↔
      ∃ U : H1Compl (roundMetric (E := E) (n := n)),
        (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
        (fun x => halfFactor p r x*u x) := by
  constructor
  · intro hu
    obtain ⟨hval,G,hG,hGn⟩ := (weightedWeakH1_half_density_iff p hp r u).mp hu
    obtain ⟨U,hU,_hE⟩ := weakH1_function_exists_completion_energy
      (roundMetric (E := E) (n := n)) _ hval G hG hGn
    exact ⟨U,hU⟩
  · rintro ⟨U,hU⟩
    obtain ⟨hval,G,hG,hGn⟩ := H1ComplToLp_memW1pIntrinsicLp (roundMetric (E := E) (n := n)) U
    exact (weightedWeakH1_half_density_iff p hp r u).mpr
      ⟨hval.ae_eq hU,G,hG.congr_fun_ae hU,hGn⟩

/-- The weighted function and its given actual weak gradient have the
original mass, mean and energy in the true full half-density H¹ domain. -/
theorem weighted_weak_exists_gauge_mass_mean_energy (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (weightedSphereVolume (n := n) p r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r)) :
    ∃ U : H1Compl (roundMetric (E := E) (n := n)),
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
        (fun x => halfFactor p r x*u x) ∧
      ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2=∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r ∧
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
        smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth (n := n) p r)⟫_ℝ=
        ∫ x,u x ∂weightedSphereVolume (n := n) p r ∧
      potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) U=
        ∫ x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂weightedSphereVolume (n := n) p r := by
  obtain ⟨U,hU,hM,hE⟩ := half_density_weak_exists_completion_mass_energy p hp r u G
    ((weightedSphere_memLp_iff p hp r u).mp hu) hG ((weightedSphere_memLp_iff p hp r _).mp hGn)
  refine ⟨U,hU,?_,?_,?_⟩
  · rw [weightedSphereVolume_integral]; exact hM
  · rw [weightedSphereVolume_integral]
    exact completion_half_density_equilibrium_pairing p r u U hU
  · rw [weightedSphereVolume_integral,← physicalPotential_eq_drift]
    exact hE

/-- Every actual full H¹ state has an inverse half-density representative
in the original weighted weak domain, with the same mass and exact energy. -/
theorem completion_exists_inverse_weighted_weak_mass_energy (p : E) (hp : ‖p‖=1) (r : ℝ)
    (U : H1Compl (roundMetric (E := E) (n := n))) :
    ∃ (u : sphere (0 : E) 1 → ℝ) (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x),
      MemLp u 2 (weightedSphereVolume (n := n) p r) ∧
      HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G ∧
      MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r) ∧
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
        (fun x => halfFactor p r x*u x) ∧
      ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2=∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r ∧
      potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) U=
        ∫ x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂weightedSphereVolume (n := n) p r := by
  let g := roundMetric (E := E) (n := n)
  let J := H1ComplToLp g
  obtain ⟨G0,hG0,hGn0,_hE0⟩ := H1ComplToLp_exists_weak_gradient_energy g U
  let u := fun x => halfFactor p (-r) x*(J U x)
  let G := halfDensityWeakGradient p (-r) (J U) G0
  obtain ⟨hu,hG,hGn⟩ := hG0.smooth_mul_witness (by norm_num : (1 : ℝ≥0∞)≤2) (Lp.memLp _) hGn0
    (halfFactor_smooth (n := n) p (-r))
  have huW : MemLp u 2 (weightedSphereVolume (n := n) p r) := (weightedSphere_memLp_iff p hp r u).mpr hu
  have hGnW : MemLp (metricNorm g G) 2 (weightedSphereVolume (n := n) p r) :=
    (weightedSphere_memLp_iff p hp r _).mpr hGn
  have hJU : (J U : sphere (0 : E) 1 → ℝ)=ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g]
      (fun x => halfFactor p r x*u x) := Eventually.of_forall fun x => by
    dsimp only [u]
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  obtain ⟨A,hA,hM,_hm,hE⟩ := weighted_weak_exists_gauge_mass_mean_energy p hp r u G huW hG hGnW
  have hAU : A=U := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    apply Lp.ext
    exact hA.trans hJU.symm
  rw [hAU] at hM hE
  exact ⟨u,G,huW,hG,hGnW,hJU,hM,hE⟩

/-- The exact optimal physical rate applies to every original weighted
distributional weak H¹ observable. Only its true weighted mean-zero
constraint and given distributional gradient are inputs. -/
theorem actual_weighted_weakH1_gap (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ)
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (weightedSphereVolume (n := n) p r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r))
    (hmean : (∫ x,u x ∂weightedSphereVolume (n := n) p r)=0) :
    weightedGap (n := n) p r*(∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r) ≤
      ∫ x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂weightedSphereVolume (n := n) p r := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨U,_hU,hM,hm,hE⟩ := weighted_weak_exists_gauge_mass_mean_energy p hp r u G hu hG hGn
  obtain ⟨e,_A,_hen,_hep,⟨c,_hc,hce⟩,_hAn,_hAo,_hAE,_hAw,hmin⟩ :=
    actual_weighted_gap_full_H1_minimum (n := n) p hp r
  have ho : ⟪H1ComplToLp g U,smoothToLp g e⟫_ℝ=0 := by
    rw [hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),
      real_inner_smul_right,hm,hmean,mul_zero]
  have hh := hmin U ho
  rwa [hM,hE] at hh

omit [NeZero n] in
/-- Rayleigh values over the entire original weighted distributional weak
H¹ domain, using a given genuine weak gradient and normalized weighted mass. -/
def weightedWeakRayleighValues (p : E) (r : ℝ) : Set ℝ :=
  {a | ∃ (u : sphere (0 : E) 1 → ℝ) (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x),
    MemLp u 2 (weightedSphereVolume (n := n) p r) ∧
    HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G ∧
    MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r) ∧
    (∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r)=1 ∧
    (∫ x,u x ∂weightedSphereVolume (n := n) p r)=0 ∧
    (∫ x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂weightedSphereVolume (n := n) p r)=a}

/-- An actual smooth physical eigenfunction belongs to the entire weighted
weak domain and attains the same normalized Rayleigh value. -/
theorem weighted_gap_mem_weakRayleighValues (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedGap (n := n) p r ∈ weightedWeakRayleighValues (n := n) p r := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨_hpos,f,hM,hm,hE,_heig,_hne,_hmin⟩ := actual_weighted_gap_spec (n := n) p hp r
  have hu : MemLp (f : sphere (0 : E) 1 → ℝ) 2
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g) :=
    (MemW1pIntrinsicLp_of_contMDiff g 2 f.contMDiff).1
  have hG : HasWeakRiemannianGradLp g (f : sphere (0 : E) 1 → ℝ) (gradFun g f) :=
    Analysis.Sobolev.Equivalence.hasWeakRiemannianGradLp_gradFun g f.contMDiff
  have hGn : MemLp (metricNorm g (gradFun g f)) 2
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g) :=
    smoothMetricGrad_memLp g ⟨f,f.contMDiff⟩
  refine ⟨f,gradFun g f,(weightedSphere_memLp_iff p hp r _).mpr hu,hG,
    (weightedSphere_memLp_iff p hp r _).mpr hGn,?_,?_,?_⟩
  · rw [weightedSphereVolume_integral]; exact hM
  · rw [weightedSphereVolume_integral]; exact hm
  · rw [weightedSphereVolume_integral]
    exact hE

/-- The original smooth-core gap is exactly the attained minimum over
all weighted distributional weak H¹ states, not merely a core estimate. -/
theorem actual_weighted_weakH1_gap_sInf (p : E) (hp : ‖p‖=1) (r : ℝ) :
    sInf (weightedWeakRayleighValues (n := n) p r)=weightedGap (n := n) p r := by
  have hmem := weighted_gap_mem_weakRayleighValues (n := n) p hp r
  have hleast : ∀ a ∈ weightedWeakRayleighValues (n := n) p r,weightedGap (n := n) p r≤a := by
    intro a ha
    obtain ⟨u,G,hu,hG,hGn,hM,hm,hE⟩ := ha
    have h := actual_weighted_weakH1_gap p hp r u G hu hG hGn hm
    simpa only [hM,hE,mul_one] using h
  exact le_antisymm (csInf_le ⟨weightedGap (n := n) p r,hleast⟩ hmem)
    (le_csInf ⟨weightedGap (n := n) p r,hmem⟩ hleast)

/-- The sharp rate is the largest constant valid on the entire original
weighted weak H¹ domain, including all nonsmooth observables. -/
theorem actual_weighted_weakH1_rate_iff (p : E) (hp : ‖p‖=1) (r c : ℝ) :
    (∀ (u : sphere (0 : E) 1 → ℝ) (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x),
      MemLp u 2 (weightedSphereVolume (n := n) p r) →
      HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G →
      MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (weightedSphereVolume (n := n) p r) →
      (∫ x,u x ∂weightedSphereVolume (n := n) p r)=0 →
      c*(∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r) ≤
        ∫ x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂weightedSphereVolume (n := n) p r) ↔
    c≤weightedGap (n := n) p r := by
  constructor
  · intro hc
    obtain ⟨u,G,hu,hG,hGn,hM,hm,hE⟩ := weighted_gap_mem_weakRayleighValues (n := n) p hp r
    have h := hc u G hu hG hGn hm
    simpa only [hM,hE,mul_one] using h
  · intro hc u G hu hG hGn hm
    have hmass : 0≤∫ x,(u x)^2 ∂weightedSphereVolume (n := n) p r := integral_nonneg fun x => sq_nonneg _
    exact (mul_le_mul_of_nonneg_right hc hmass).trans (actual_weighted_weakH1_gap p hp r u G hu hG hGn hm)

end DFLWeightedWeakH1
