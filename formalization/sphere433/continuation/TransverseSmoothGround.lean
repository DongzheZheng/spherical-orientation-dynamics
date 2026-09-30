import continuation.ActualTiltProfileWitness

/-! The actual auxiliary ground yields a true globally smooth physical
first-transverse eigenstate at the actual minimum, with every finite pole
order derived from one genuine smooth auxiliary sphere representative. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLSphere DFL.Spectral
namespace DFLTransverseSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- Unconditional actual first-transverse smooth eigenstate for every
physical n≥1. Neither smooth pole profiles nor minimum attainment is an
input. Original latitude normalization and actual nonzero state remain
part of the conclusion. -/
theorem actual_transverse_smooth_ground_exists (p a : E)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0) (r : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm (n+2) r v = 1 ∧
      ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (transverseMode p a v) ∧ transverseMode p a v ≠ 0 ∧
      ∀ x : sphere (0 : E) 1, weightedRoundApply (n := n) p r (transverseMode p a v) x =
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*transverseMode p a v x := by
  obtain ⟨psi,hpsi,hpos,s,hs,hps⟩ := original_tilt_ground_actual_witness n (n : ℝ) r ((n : ℝ)/2)
  let v := weightedProfileFromHalfDensity r psi
  have hv : ContDiff ℝ 2 v := weightedProfileFromHalfDensity_smooth r psi hpsi.smooth
  have hvp : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t := weightedProfileFromHalfDensity_positive r psi hpos
  have hvn : latitudeNorm (n+2) r v = 1 := by
    rw [weightedProfileFromHalfDensity_norm,hpsi.normalized]
  have hvsm : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (transverseMode p a v) :=
    actual_auxiliary_profile_transverse_contMDiff p a hp r psi s hs hps
  have ht : ((n+2 : ℕ) : ℝ)/2-1 = (n : ℝ)/2 := by push_cast; ring
  have hpe : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply (n+2) (n : ℝ) r (((n+2 : ℕ) : ℝ)/2-1) psi t =
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*psi t := by
    simpa only [ht] using hpsi.eigen
  have hve := weightedProfileFromHalfDensity_eigen (n+2) 1 (n : ℝ) r _ psi hpsi.smooth hpe
  refine ⟨v,hv,hvp,hvn,hvsm,transverseMode_nonzero p a ha hpa v (hvp 0 (by norm_num)),?_⟩
  exact transverseMode_weighted_eigen p a hp hpa r _ v hv hve

end DFLTransverseSphere
