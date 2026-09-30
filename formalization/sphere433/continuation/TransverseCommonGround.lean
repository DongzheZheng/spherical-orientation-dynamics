import continuation.TransverseSmoothGround

/-! A single actual normalized auxiliary ground defines every transverse
mode on the physical sphere. Its true smooth auxiliary representative
supplies all finite pole orders for all ambient amplitudes. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLSphere DFL.Spectral
namespace DFLTransverseSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- One genuine positive normalized latitude ground gives all actual
smooth transverse modes and their true pointwise weighted equations. -/
theorem actual_transverse_common_ground_exists (p : E) (hp : ‖p‖=1) (r : ℝ) :
    ∃ v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (n+2) r v=1 ∧
      LatitudeEigenEquation (n+2) 1 (n : ℝ) r
        (roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)) v ∧
      (∀a : E,ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (transverseMode p a v)) ∧
      ∀a : E,⟪a,p⟫_ℝ=0 → ∀x : sphere (0 : E) 1,
        weightedRoundApply (n := n) p r (transverseMode p a v) x=
          roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*transverseMode p a v x := by
  obtain ⟨psi,hpsi,hpos,s,hs,hps⟩ := original_tilt_ground_actual_witness n (n : ℝ) r ((n : ℝ)/2)
  let v := weightedProfileFromHalfDensity r psi
  have hv := weightedProfileFromHalfDensity_smooth r psi hpsi.smooth
  have hvp := weightedProfileFromHalfDensity_positive r psi hpos
  have hvn : latitudeNorm (n+2) r v=1 := by
    rw [weightedProfileFromHalfDensity_norm,hpsi.normalized]
  have ht : (((n+2 : ℕ) : ℝ)/2-1)=(n : ℝ)/2 := by push_cast; ring
  have hpe : ∀t∈Icc (-1 : ℝ) 1,tiltApply (n+2) (n : ℝ) r
      (((n+2 : ℕ) : ℝ)/2-1) psi t=roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*psi t := by
    simpa only [ht] using hpsi.eigen
  have hve := weightedProfileFromHalfDensity_eigen (n+2) 1 (n : ℝ) r _ psi hpsi.smooth hpe
  refine ⟨v,hv,hvp,hvn,?_,?_,?_⟩
  · intro t ht
    exact hve t ht
  · intro a
    exact actual_auxiliary_profile_transverse_contMDiff p a hp r psi s hs hps
  · intro a ha
    exact transverseMode_weighted_eigen p a hp ha r _ v hv hve
end DFLTransverseSphere
