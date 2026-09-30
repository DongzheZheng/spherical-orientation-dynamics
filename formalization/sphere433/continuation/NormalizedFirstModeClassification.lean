import continuation.FirstAngularIntegratedEquality
import continuation.SphereFirstModeRecovery
import continuation.TransverseCommonGround

/-! Every actual normalized smooth first minimizer on the physical sphere
has one common transverse ground profile. The latitude ground is selected
once, before quantifying over the first minimizers. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Set Metric Module MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLSphere DFL.Spectral DFLPhysicalGap DFLPhysicalLatitude
open DFLMeanSphere DFLCotSphere DFLTransverseSphere DFLFullSphereMeanZero
open DFLFirstAngularEquality
namespace DFLNormalizedFirstMode

/-- A given original positive auxiliary ground represents every actual
normalized physical first minimizer, with a single ambient transverse
amplitude and pointwise equality on the whole sphere. -/
theorem actual_gap_minimizer_same_ground_mode (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hM : weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1)
    (hm : weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0)
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=
      weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) :
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      ∀x : PhysicalSphere k,f x=transverseMode (EuclideanSpace.single 0 1) a v x := by
  have hmean := actual_gap_minimizer_angular_mean_zero k hk r hr f hM hm hE
  have hAngular := actual_gap_minimizer_angular_energy_equality k hk r hr f hM hm hE
  have hScalar := actual_gap_minimizer_scalar_energy_equality k hk r hr f hM hm hE
  simp_rw [cot_transverse_reduced_eq] at hScalar
  have hEq : (∫s : ℝ,cotDeviationEnergy (canonicalAxisSphere k) f r s)=
      roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)*
        ∫s : ℝ,cotTransverseMass (canonicalAxisSphere k) f r s := by
    simpa only [Nat.cast_add,Nat.cast_one] using hAngular.trans hScalar
  obtain ⟨a,ha⟩ := cot_transverse_mean_zero_equality_same_ground_mode hk
    (canonicalAxisSphere k) f r v hv hpos heig hmean hEq
  refine ⟨(a : PhysicalAmbient k),?_,ha⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp a.property

/-- One actual positive normalized original latitude ground defines all
the normalized smooth first minimizers. It also gives genuine smooth
weighted eigenfunctions for every axis-orthogonal ambient amplitude. -/
theorem actual_first_minimizers_common_ground_exists (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (k+3) r v=1 ∧
      LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v ∧
      (∀a : PhysicalAmbient k,ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞
        (transverseMode (EuclideanSpace.single 0 1) a v)) ∧
      (∀a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 → ∀x : PhysicalSphere k,
        weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r
          (transverseMode (EuclideanSpace.single 0 1) a v) x=
            roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)*
              transverseMode (EuclideanSpace.single 0 1) a v x) ∧
      ∀f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯,
        weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1 →
        weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0 →
        weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=
          weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r →
        ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
          ∀x : PhysicalSphere k,f x=transverseMode (EuclideanSpace.single 0 1) a v x := by
  obtain ⟨v,hv,hpos,hN,heig,hSmooth,hPDE⟩ := actual_transverse_common_ground_exists
    (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r
  have hN' : latitudeNorm (k+3) r v=1 := by simpa [Nat.add_assoc] using hN
  have heig' : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v := by
    simpa [Nat.add_assoc] using heig
  refine ⟨v,hv,hpos,hN',heig',hSmooth,hPDE,?_⟩
  intro f hM hm hE
  exact actual_gap_minimizer_same_ground_mode k hk r hr v hv hpos heig' f hM hm hE

end DFLNormalizedFirstMode
