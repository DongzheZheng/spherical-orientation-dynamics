import continuation.WeightedWeakH1Gauge
import continuation.WeakFirstEigenspace

/-! Equality in the original exponentially weighted distributional weak
H1 sphere inequality. The function and its genuine weak tangent gradient
are the original objects; a common ground profile is chosen once for all
equality states. -/
noncomputable section
set_option maxHeartbeats 1400000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLPhysicalHalfDensity DFLPhysicalGap DFLPhysicalLatitude DFL.Spectral
open DFLWeakPhysical DFLWeightedWeakH1
open DFLWeakH1Completion
namespace DFLOriginalWeakFirst
private local instance (k : ℕ) : MeasurableSpace (PhysicalSphere k) := borel (PhysicalSphere k)
private local instance (k : ℕ) : BorelSpace (PhysicalSphere k) := ⟨rfl⟩

private theorem original_weighted_ae_iff (k : ℕ) (r : ℝ)
    (f h : PhysicalSphere k → ℝ) :
    f=ᵐ[weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r] h ↔
      f=ᵐ[riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
        (roundMetric (E := PhysicalAmbient k) (n := k+1))] h := by
  let μ := riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
    (roundMetric (E := PhysicalAmbient k) (n := k+1))
  let d := fun x : PhysicalSphere k => ENNReal.ofReal
    (Real.exp (r*⟪(EuclideanSpace.single 0 1 : PhysicalAmbient k),(x : PhysicalAmbient k)⟫_ℝ))
  have hc : Continuous (fun x : PhysicalSphere k =>
      Real.exp (r*⟪(EuclideanSpace.single 0 1 : PhysicalAmbient k),(x : PhysicalAmbient k)⟫_ℝ)) := by fun_prop
  have hm : AEMeasurable d μ := (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
  have hn : ∀ᵐx ∂μ,d x≠0 := ae_of_all _ (fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  exact withDensity_ae_eq hm hn

/-- Equality for the original weighted function and its actual
distributional weak gradient gives one common transverse mode, without
smoothness or a weak eigenidentity as an input. -/
theorem original_weighted_weak_equality_same_ground_mode
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (u : PhysicalSphere k → ℝ) (G : ∀x : PhysicalSphere k,TangentSpace (𝓡 (k+1)) x)
    (hu : MemLp u 2 (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := PhysicalAmbient k) (n := k+1)) G) 2
      (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hmean : (∫x,u x ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=0)
    (heq : (∫x,(roundMetric (E := PhysicalAmbient k) (n := k+1)).inner x (G x) (G x)
      ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=
        physicalGap k r*∫x,(u x)^2
          ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) :
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      u=ᵐ[weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r]
        transverseMode (EuclideanSpace.single 0 1) a v := by
  obtain ⟨U,hU,hM,hm,hE⟩ := weighted_weak_exists_gauge_mass_mean_energy (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r u G hu hG hGn
  have horth := hm.trans hmean
  have hQ : potentialEnergy (roundMetric (E := PhysicalAmbient k) (n := k+1))
      (physicalPotential (n := k+1) (EuclideanSpace.single 0 1) r) U=
        physicalGap k r*‖H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U‖^2 := by
    rw [physicalPotential_eq_drift,hE,hM]
    exact heq
  obtain ⟨a,ha,hMode⟩ := actual_full_H1_rayleigh_equality_same_ground_mode
    k hk r hr v hv hpos heig U horth hQ
  refine ⟨a,ha,(original_weighted_ae_iff k r _ _).mpr ?_⟩
  filter_upwards [hU,hMode] with x hx hm
  exact mul_left_cancel₀ (Real.exp_pos _).ne' (hx.symm.trans hm)

/-- The complete original weighted weak equality condition is equivalent
to the fixed common transverse mode. The gradient is the actual arbitrary
distributional tangent gradient supplied with the original observable. -/
theorem original_weighted_weak_equality_iff_same_ground_mode
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (hSmooth : ∀a : PhysicalAmbient k,ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞
      (transverseMode (EuclideanSpace.single 0 1) a v))
    (u : PhysicalSphere k → ℝ) (G : ∀x : PhysicalSphere k,TangentSpace (𝓡 (k+1)) x)
    (hu : MemLp u 2 (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := PhysicalAmbient k) (n := k+1)) G) 2
      (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hmean : (∫x,u x ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=0) :
    (∫x,(roundMetric (E := PhysicalAmbient k) (n := k+1)).inner x (G x) (G x)
      ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=
        physicalGap k r*∫x,(u x)^2
          ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r ↔
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      u=ᵐ[weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r]
        transverseMode (EuclideanSpace.single 0 1) a v := by
  constructor
  · exact original_weighted_weak_equality_same_ground_mode k hk r hr v hv hpos heig u G hu hG hGn hmean
  · rintro ⟨a,ha,hrep⟩
    let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
    let p : PhysicalAmbient k := EuclideanSpace.single 0 1
    obtain ⟨U,hU,hM,_hm,hE⟩ := weighted_weak_exists_gauge_mass_mean_energy (n := k+1)
      p (by simp [p]) r u G hu hG hGn
    have hround := (original_weighted_ae_iff k r _ _).mp hrep
    have hMode : (H1ComplToLp g U : PhysicalSphere k → ℝ)=ᵐ[riemannianVolumeMeasure
        (𝓡 (k+1)) (PhysicalSphere k) g] (fun x => halfFactor p r x*transverseMode p a v x) := by
      filter_upwards [hU,hround] with x hx hrx
      rw [hx,hrx]
    have hweak := (actual_gauged_weak_first_iff_mode k hk r hr v hv hpos heig hSmooth U).mpr ⟨a,ha,hMode⟩
    have hV : MemLp (physicalPotential (n := k+1) p r) ∞
        (riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k) g) := by
      rw [physicalPotential_eq_drift]
      exact driftPotential_memLp_top p r
    have hdiag : potentialEnergy g (physicalPotential (n := k+1) p r) U=
        physicalGap k r*‖H1ComplToLp g U‖^2 := by
      have hh : potentialForm (H1ComplToLp g) (boundedPotentialMultiplication _ hV) U U=
          physicalGap k r*⟪H1ComplToLp g U,H1ComplToLp g U⟫_ℝ := by
        rw [actual_potential_form_eq]
        exact hweak U
      rw [actual_potential_form_diag,real_inner_self_eq_norm_sq] at hh
      exact hh
    rwa [physicalPotential_eq_drift,hE,hM] at hdiag

/-- A single actual positive normalized original auxiliary ground
classifies equality for every original weighted weak H1 observable and its
given distributional gradient. No smoothness restriction remains on u. -/
theorem original_weighted_weak_equality_common_ground_exists
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (k+3) r v=1 ∧
      LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v ∧
      ∀(u : PhysicalSphere k → ℝ) (G : ∀x : PhysicalSphere k,TangentSpace (𝓡 (k+1)) x),
        MemLp u 2 (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) →
        HasWeakRiemannianGradLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) u G →
        MemLp (metricNorm (roundMetric (E := PhysicalAmbient k) (n := k+1)) G) 2
          (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) →
        (∫x,u x ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=0 →
        ((∫x,(roundMetric (E := PhysicalAmbient k) (n := k+1)).inner x (G x) (G x)
          ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=
            physicalGap k r*∫x,(u x)^2
              ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r ↔
        ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
          u=ᵐ[weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r]
            transverseMode (EuclideanSpace.single 0 1) a v) := by
  obtain ⟨v,hv,hpos,hN,heig,hSmooth,_hClass,_hUnique,_hDim⟩ :=
    actual_first_eigenspace_common_ground_exists k hk r hr
  refine ⟨v,hv,hpos,hN,heig,?_⟩
  intro u G hu hG hGn hmean
  exact original_weighted_weak_equality_iff_same_ground_mode k hk r hr v hv hpos heig hSmooth u G hu hG hGn hmean

end DFLOriginalWeakFirst
