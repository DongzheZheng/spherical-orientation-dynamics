import continuation.NormalizedFirstModeClassification
import continuation.WeightedEigenNormalization
import continuation.TransverseModeDimension
import continuation.PhysicalGapIdentification

/-! The original complete first eigenspace, with one fixed positive
latitude ground. Normalization and restoration of the original amplitude
use the actual weighted mass of the same eigenfunction. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLSphere DFL.Spectral DFLPhysicalLatitude DFLTransverseSphere
open DFLNormalizedFirstMode
namespace DFLPhysicalGap

/-- For a fixed original positive transverse ground, every genuine smooth
first eigenstate has the original transverse form, with arbitrary amplitude.
The equation is the actual round weighted differential equation. -/
theorem actual_first_eigen_same_ground_mode (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (u : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hu : ∀x,weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r u x=
      physicalGap k r*u x) :
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      ∀x : PhysicalSphere k,u x=transverseMode (EuclideanSpace.single 0 1) a v x := by
  by_cases hz : (u : PhysicalSphere k → ℝ)=0
  · refine ⟨0,by simp,?_⟩
    intro x
    have hx : u x=0 := congrFun hz x
    simp only [hx,transverseMode,inner_zero_left,zero_mul]
  have hgap : 0<physicalGap k r :=
    (actual_weighted_gap_spec (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k)
      (by simp) r).1
  obtain ⟨c,hc,hM,hm,hE⟩ := actual_weighted_eigen_normalized (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r (physicalGap k r) hgap u hz hu
  obtain ⟨a,ha,hrep⟩ := actual_gap_minimizer_same_ground_mode k hk r hr v hv hpos heig
    (scaleObservable c u) hM hm hE
  refine ⟨c⁻¹ •a,by simp only [real_inner_smul_left,ha,mul_zero],?_⟩
  intro x
  have hx : c*u x=⟪a,(x : PhysicalAmbient k)⟫_ℝ * v ⟪EuclideanSpace.single 0 1,(x : PhysicalAmbient k)⟫_ℝ :=
    hrep x
  have hcx := congrArg (fun z : ℝ=>c⁻¹*z) hx
  rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] at hcx
  simpa only [transverseMode,real_inner_smul_left,mul_assoc] using hcx

/-- One actual positive normalized latitude ground describes the entire
smooth first eigenspace. It gives smooth eigenfunctions for every transverse
amplitude, and the amplitude is unique. The transverse function space has
dimension k+1, the physical sphere dimension. -/
theorem actual_first_eigenspace_common_ground_exists (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (k+3) r v=1 ∧
      LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v ∧
      (∀a : PhysicalAmbient k,ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞
        (transverseMode (EuclideanSpace.single 0 1) a v)) ∧
      (∀u : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯,
        (∀x,weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r u x=
          physicalGap k r*u x) ↔
        ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
          ∀x : PhysicalSphere k,u x=transverseMode (EuclideanSpace.single 0 1) a v x) ∧
      (∀a b : PhysicalAmbient k,
        (∀x : PhysicalSphere k,transverseMode (EuclideanSpace.single 0 1) a v x=
          transverseMode (EuclideanSpace.single 0 1) b v x) → a=b) ∧
      finrank ℝ (transverseMode_range (EuclideanSpace.single 0 1 : PhysicalAmbient k) v)=k+1 := by
  obtain ⟨v,hv,hpos,hN,heig,hSmooth,hPDE,_hClass⟩ :=
    actual_first_minimizers_common_ground_exists k hk r hr
  refine ⟨v,hv,hpos,hN,heig,hSmooth,?_,?_,?_⟩
  · intro u
    constructor
    · exact actual_first_eigen_same_ground_mode k hk r hr v hv hpos heig u
    · rintro ⟨a,ha,hrep⟩ x
      have hfun : (u : PhysicalSphere k → ℝ)=transverseMode (EuclideanSpace.single 0 1) a v := funext hrep
      rw [hfun,hPDE a ha x,actual_physical_gap_eq_transverse]
      simp only [Nat.cast_add,Nat.cast_one]
  · intro a b hab
    exact transverseMode_amplitude_injective
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) v hpos (funext hab)
  · exact transverseMode_range_finrank (n := k+1)
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) v hpos

end DFLPhysicalGap
