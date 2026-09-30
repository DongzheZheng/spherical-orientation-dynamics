import continuation.WeightedWeakH1Gauge
import continuation.PhysicalGapIdentification

/-! The original DFL sharp rate over the entire weighted distributional
weak H¹ domain on every physical sphere S^(k+1), including the circle.
The value is the original transverse auxiliary ground minimum, now
identified with the genuine all-domain Rayleigh infimum. -/
noncomputable section
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DFLWeakH1Completion DFLWeightedWeakH1 DFLPhysicalLatitude DFLPhysicalGap DFLSphere
namespace DFLOriginalWeakGap
private local instance (k : ℕ) : MeasurableSpace (PhysicalSphere k) := borel (PhysicalSphere k)
private local instance (k : ℕ) : BorelSpace (PhysicalSphere k) := ⟨rfl⟩

/-- The original conjectured best rate bounds every genuine weighted weak
H¹ observable, in all sphere dimensions at least one and all real fields. -/
theorem actual_original_weighted_weakH1_poincare (k : ℕ) (r : ℝ)
    (u : PhysicalSphere k → ℝ)
    (G : ∀ x : PhysicalSphere k, TangentSpace (𝓡 (k+1)) x)
    (hu : MemLp u 2 (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hG : HasWeakRiemannianGradLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := PhysicalAmbient k) (n := k+1)) G) 2
      (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r))
    (hmean : (∫ x,u x ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=0) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)*
      (∫ x,(u x)^2 ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) ≤
    ∫ x,(roundMetric (E := PhysicalAmbient k) (n := k+1)).inner x (G x) (G x)
      ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r := by
  have h := actual_weighted_weakH1_gap (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r u G hu hG hGn hmean
  change physicalGap k r*_≤_ at h
  rwa [actual_physical_gap_eq_transverse] at h

/-- The original rate is exactly the attained infimum over all weighted
distributional weak H¹ Rayleigh values, with no smooth-core restriction. -/
theorem actual_original_weighted_weakH1_gap_sInf (k : ℕ) (r : ℝ) :
    sInf (weightedWeakRayleighValues (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=
      roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
  rw [actual_weighted_weakH1_gap_sInf _ (by simp)]
  exact actual_physical_gap_eq_transverse k r

/-- The conjectured rate is the largest possible Poincaré constant on the
original entire weighted weak H¹ domain, including its circle endpoint. -/
theorem actual_original_weighted_weakH1_rate_iff (k : ℕ) (r c : ℝ) :
    (∀ (u : PhysicalSphere k → ℝ) (G : ∀ x : PhysicalSphere k, TangentSpace (𝓡 (k+1)) x),
      MemLp u 2 (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) →
      HasWeakRiemannianGradLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) u G →
      MemLp (metricNorm (roundMetric (E := PhysicalAmbient k) (n := k+1)) G) 2
        (weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) →
      (∫ x,u x ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)=0 →
      c*(∫ x,(u x)^2 ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) ≤
      ∫ x,(roundMetric (E := PhysicalAmbient k) (n := k+1)).inner x (G x) (G x)
        ∂weightedSphereVolume (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) ↔
    c≤roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
  have h := actual_weighted_weakH1_rate_iff (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r c
  change _↔c≤physicalGap k r at h
  rwa [actual_physical_gap_eq_transverse] at h

end DFLOriginalWeakGap
