import continuation.WeightedWeakH1Gauge

/-! The actual normalized von Mises--Fisher probability measure, its
entire distributional weak H¹ domain, and its sharp original Poincaré rate.
Normalization is a genuine scalar operation on the actual sphere measure. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFLPhysicalGap DFLWeightedWeakH1 DFLWeakH1Completion
namespace DFLNormalizedVMF
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- Actual total mass of the exponential density against genuine round
Riemannian volume, rather than an independently specified normalizer. -/
def spherePartition (p : E) (r : ℝ) : ℝ≥0∞ := weightedSphereVolume (n := n) p r univ

/-- The original von Mises--Fisher law is the actual weighted measure
scaled by the inverse of its own total mass. -/
def normalizedSphereVolume (p : E) (r : ℝ) : Measure (sphere (0 : E) 1) :=
  (spherePartition (n := n) p r)⁻¹ • weightedSphereVolume (n := n) p r

/-- The true partition function is finite and strictly positive. -/
theorem spherePartition_pos_finite (p : E) (hp : ‖p‖=1) (r : ℝ) :
    0 < spherePartition (n := n) p r ∧ spherePartition (n := n) p r < (∞ : ℝ≥0∞) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let : IsFiniteMeasure mu := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let : Nonempty (sphere (0 : E) 1) := ⟨⟨p,by rw [mem_sphere_zero_iff_norm];exact hp⟩⟩
  have hmu : 0 < mu univ := isOpen_univ.measure_pos mu univ_nonempty
  have hcomp := weightedSphereVolume_comparison (n := n) p hp r
  have hu := Measure.le_iff'.mp hcomp.1 univ
  have hl := Measure.le_iff'.mp hcomp.2 univ
  simp only [Measure.smul_apply,smul_eq_mul] at hu hl
  refine ⟨?_,lt_of_le_of_lt hu (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu univ))⟩
  by_contra h
  have hz : spherePartition (n := n) p r=0 := le_antisymm (le_of_not_gt h) bot_le
  change mu univ≤ENNReal.ofReal (Real.exp |r|)*spherePartition (n := n) p r at hl
  rw [hz,mul_zero] at hl
  exact hmu.not_ge hl

/-- The normalized actual sphere law is a probability measure. -/
theorem normalizedSphereVolume_probability (p : E) (hp : ‖p‖=1) (r : ℝ) :
    IsProbabilityMeasure (normalizedSphereVolume (n := n) p r) := by
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  constructor
  change (spherePartition (n := n) p r)⁻¹*spherePartition (n := n) p r=1
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- Recovering the actual unnormalized law proves that normalization
changes neither its null sets nor its weak-domain admissibility. -/
theorem weightedSphereVolume_eq_partition_smul_normalized (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedSphereVolume (n := n) p r=
      spherePartition (n := n) p r • normalizedSphereVolume (n := n) p r := by
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  rw [normalizedSphereVolume,smul_smul,ENNReal.mul_inv_cancel hpos.ne' hfin.ne,one_smul]

/-- Normalized and unnormalized actual weighted L² domains coincide. -/
theorem normalizedSphere_memLp_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) :
    MemLp f 2 (normalizedSphereVolume (n := n) p r) ↔
      MemLp f 2 (weightedSphereVolume (n := n) p r) := by
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  constructor
  · intro hf
    rw [weightedSphereVolume_eq_partition_smul_normalized p hp r]
    exact hf.smul_measure hfin.ne
  · intro hf
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hpos.ne')

/-- The actual normalized probability law has exactly the original
weighted null sets, so equality states keep the same a.e. meaning. -/
theorem normalizedSphere_ae_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (P : sphere (0 : E) 1 → Prop) :
    (∀ᵐx ∂normalizedSphereVolume (n := n) p r,P x) ↔
      ∀ᵐx ∂weightedSphereVolume (n := n) p r,P x := by
  obtain ⟨_hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hfin.ne)

/-- Every actual scalar integral has the original common normalization
factor, including mass, mean, and genuine weak-gradient energy. -/
theorem normalizedSphere_integral (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) :
    (∫x,f x ∂normalizedSphereVolume (n := n) p r)=
      (spherePartition (n := n) p r).toReal⁻¹*∫x,f x ∂weightedSphereVolume (n := n) p r := by
  rw [normalizedSphereVolume,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]

/-- Mass-energy identities, in particular equality in the sharp bound,
are identical under the genuine probability normalization. -/
theorem normalizedSphere_integral_eq_multiple_iff (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (f h : sphere (0 : E) 1 → ℝ) :
    (∫x,f x ∂normalizedSphereVolume (n := n) p r)=lam*∫x,h x ∂normalizedSphereVolume (n := n) p r ↔
      (∫x,f x ∂weightedSphereVolume (n := n) p r)=lam*∫x,h x ∂weightedSphereVolume (n := n) p r := by
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  have hc : (spherePartition (n := n) p r).toReal⁻¹≠0 :=
    inv_ne_zero (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  rw [normalizedSphere_integral,normalizedSphere_integral]
  have hswap : lam*((spherePartition (n := n) p r).toReal⁻¹*∫x,h x ∂weightedSphereVolume (n := n) p r)=
      (spherePartition (n := n) p r).toReal⁻¹*(lam*∫x,h x ∂weightedSphereVolume (n := n) p r) := by ring
  rw [hswap]
  constructor
  · exact mul_left_cancel₀ hc
  · intro hEq
    rw [hEq]

/-- The complete original weak H¹ domain expressed directly under the
actual normalized probability law. -/
def NormalizedWeightedWeakH1 (p : E) (r : ℝ) (u : sphere (0 : E) 1 → ℝ) : Prop :=
  MemLp u 2 (normalizedSphereVolume (n := n) p r) ∧
    ∃ G : ∀x : sphere (0 : E) 1,TangentSpace (𝓡 n) x,
      HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G ∧
      MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (normalizedSphereVolume (n := n) p r)

/-- Probability normalization preserves the entire distributional weak
H¹ domain, without a smoothness assumption. -/
theorem normalizedWeightedWeakH1_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) :
    NormalizedWeightedWeakH1 (n := n) p r u ↔ WeightedWeakH1 (n := n) p r u := by
  constructor
  · rintro ⟨hu,G,hG,hGn⟩
    exact ⟨(normalizedSphere_memLp_iff p hp r u).mp hu,G,hG,
      (normalizedSphere_memLp_iff p hp r _).mp hGn⟩
  · rintro ⟨hu,G,hG,hGn⟩
    exact ⟨(normalizedSphere_memLp_iff p hp r u).mpr hu,G,hG,
      (normalizedSphere_memLp_iff p hp r _).mpr hGn⟩

/-- Zero weighted mean is the same constraint before and after actual
probability normalization. -/
theorem normalizedSphere_mean_zero_iff (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) :
    (∫x,u x ∂normalizedSphereVolume (n := n) p r)=0 ↔
      (∫x,u x ∂weightedSphereVolume (n := n) p r)=0 := by
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  have hc : (spherePartition (n := n) p r).toReal⁻¹≠0 :=
    inv_ne_zero (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  rw [normalizedSphere_integral,mul_eq_zero]
  exact or_iff_right (by exact hc)

variable [NeZero n]

/-- The sharp original physical rate holds for every true weighted weak
H¹ observable under the actual vMF probability measure. -/
theorem actual_normalized_weakH1_gap (p : E) (hp : ‖p‖=1) (r : ℝ)
    (u : sphere (0 : E) 1 → ℝ) (G : ∀x : sphere (0 : E) 1,TangentSpace (𝓡 n) x)
    (hu : MemLp u 2 (normalizedSphereVolume (n := n) p r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (normalizedSphereVolume (n := n) p r))
    (hmean : (∫x,u x ∂normalizedSphereVolume (n := n) p r)=0) :
    weightedGap (n := n) p r*(∫x,(u x)^2 ∂normalizedSphereVolume (n := n) p r) ≤
      ∫x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂normalizedSphereVolume (n := n) p r := by
  have hh := actual_weighted_weakH1_gap p hp r u G
    ((normalizedSphere_memLp_iff p hp r u).mp hu) hG
    ((normalizedSphere_memLp_iff p hp r _).mp hGn)
    ((normalizedSphere_mean_zero_iff p hp r u).mp hmean)
  rw [normalizedSphere_integral,normalizedSphere_integral]
  have hc := mul_le_mul_of_nonneg_left hh
    (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := spherePartition (n := n) p r)))
  simpa only [mul_left_comm] using hc

/-- Actual zero-mean Rayleigh quotients over the entire normalized weak
domain, with positive mass and the genuine distributional gradient. -/
def normalizedWeakRayleighValues (p : E) (r : ℝ) : Set ℝ :=
  {a | ∃ (u : sphere (0 : E) 1 → ℝ) (G : ∀x : sphere (0 : E) 1,TangentSpace (𝓡 n) x),
    MemLp u 2 (normalizedSphereVolume (n := n) p r) ∧
    HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G ∧
    MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (normalizedSphereVolume (n := n) p r) ∧
    0<(∫x,(u x)^2 ∂normalizedSphereVolume (n := n) p r) ∧
    (∫x,u x ∂normalizedSphereVolume (n := n) p r)=0 ∧
    (∫x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂normalizedSphereVolume (n := n) p r)/
      (∫x,(u x)^2 ∂normalizedSphereVolume (n := n) p r)=a}

/-- The true full-domain minimum is attained also for the actual
normalized vMF probability law. -/
theorem normalized_gap_mem_weakRayleighValues (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedGap (n := n) p r∈normalizedWeakRayleighValues (n := n) p r := by
  obtain ⟨u,G,hu,hG,hGn,hM,hm,hE⟩ := weighted_gap_mem_weakRayleighValues (n := n) p hp r
  obtain ⟨hpos,hfin⟩ := spherePartition_pos_finite (n := n) p hp r
  have hc : 0<(spherePartition (n := n) p r).toReal⁻¹ :=
    inv_pos.mpr (ENNReal.toReal_pos hpos.ne' hfin.ne)
  refine ⟨u,G,(normalizedSphere_memLp_iff p hp r u).mpr hu,hG,
    (normalizedSphere_memLp_iff p hp r _).mpr hGn,?_,
    (normalizedSphere_mean_zero_iff p hp r u).mpr hm,?_⟩
  · rw [normalizedSphere_integral,hM,mul_one]
    exact hc
  · rw [normalizedSphere_integral,normalizedSphere_integral,hM,hE,mul_one]
    exact mul_div_cancel_left₀ _ hc.ne'

/-- The optimal Poincaré rate on the actual normalized weak domain is
exactly the proved original full-sphere gap. -/
theorem actual_normalized_weakH1_gap_sInf (p : E) (hp : ‖p‖=1) (r : ℝ) :
    sInf (normalizedWeakRayleighValues (n := n) p r)=weightedGap (n := n) p r := by
  have hmem := normalized_gap_mem_weakRayleighValues (n := n) p hp r
  have hleast : ∀a∈normalizedWeakRayleighValues (n := n) p r,weightedGap (n := n) p r≤a := by
    intro a ha
    obtain ⟨u,G,hu,hG,hGn,hM,hm,hE⟩ := ha
    rw [← hE]
    exact (le_div_iff₀ hM).mpr (actual_normalized_weakH1_gap p hp r u G hu hG hGn hm)
  exact le_antisymm (csInf_le ⟨weightedGap (n := n) p r,hleast⟩ hmem)
    (le_csInf ⟨weightedGap (n := n) p r,hmem⟩ hleast)

/-- The same exact rate is the largest constant valid for every original
weighted weak observable under the genuine vMF probability law. -/
theorem actual_normalized_weakH1_rate_iff (p : E) (hp : ‖p‖=1) (r c : ℝ) :
    (∀ (u : sphere (0 : E) 1 → ℝ) (G : ∀x : sphere (0 : E) 1,TangentSpace (𝓡 n) x),
      MemLp u 2 (normalizedSphereVolume (n := n) p r) →
      HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G →
      MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (normalizedSphereVolume (n := n) p r) →
      (∫x,u x ∂normalizedSphereVolume (n := n) p r)=0 →
      c*(∫x,(u x)^2 ∂normalizedSphereVolume (n := n) p r) ≤
        ∫x,(roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂normalizedSphereVolume (n := n) p r) ↔
    c≤weightedGap (n := n) p r := by
  constructor
  · intro hc
    obtain ⟨u,G,hu,hG,hGn,hM,hm,hE⟩ := normalized_gap_mem_weakRayleighValues (n := n) p hp r
    rw [← hE]
    exact (le_div_iff₀ hM).mpr (hc u G hu hG hGn hm)
  · intro hc u G hu hG hGn hm
    have hM : 0≤∫x,(u x)^2 ∂normalizedSphereVolume (n := n) p r := integral_nonneg fun x => sq_nonneg _
    exact (mul_le_mul_of_nonneg_right hc hM).trans (actual_normalized_weakH1_gap p hp r u G hu hG hGn hm)

end DFLNormalizedVMF
