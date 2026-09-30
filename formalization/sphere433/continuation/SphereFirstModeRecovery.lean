import continuation.CotTransverseEquality
import continuation.TransverseSphereMode

/-! Recovery of the original separated first mode on the entire actual
sphere. The proved cot inverse covers the complement of its two null poles;
actual Riemannian open positivity and continuity recover both poles. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold MeasureTheory Metric Module Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLTransverseSphere
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- True cot equality determines continuous functions on the complete
actual sphere, including its two physical poles. -/
theorem cot_continuous_sphere_eq (p : sphere (0 : E) 1)
    (F G : sphere (0 : E) 1 → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hCot : ∀q : PolarDir p × ℝ,F (cotSpherePD (n := n) p q)=G (cotSpherePD (n := n) p q)) : F=G := by
  let mu := riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))
  let _ : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
  have hTarget : ∀ᵐx∂mu,x∈polarTarget p := ae_iff.mpr (round_sphere_polar_complement_volume_zero (n := n) p)
  have hAE : F=ᵐ[mu] G := by
    filter_upwards [hTarget] with x hx
    have hh := hCot ((cotSpherePD (n := n) p).symm x)
    rw [cotSpherePD_right_inverse p x hx] at hh
    exact hh
  exact MeasureTheory.Measure.eq_of_ae_eq hAE hF hG

omit [FiniteDimensional ℝ E] in
/-- The original angular linear mode is exactly the actual ambient
coordinate orthogonal to the physical axis, multiplied by angular scale. -/
theorem cot_complement_coordinate (p : sphere (0 : E) 1) (a : (ℝ ∙ (p : E))ᗮ) (q : PolarDir p × ℝ) :
    ⟪(a : E),(cotSpherePD (n := n) p q : E)⟫_ℝ=cotAngularScale q.2*⟪a,(q.1 : (ℝ ∙ (p : E))ᗮ)⟫_ℝ := by
  have ha : ⟪(a : E),(p : E)⟫_ℝ=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp a.property
  rw [cotSpherePD_ambient]
  simp only [real_inner_smul_right,inner_add_right,ha,mul_zero,zero_add]
  rfl

/-- With a specified common positive original ground profile, actual
transverse equality and vanishing actual angular mean recover one ambient
first mode on the whole sphere. No profile is chosen separately for fibers. -/
theorem cot_transverse_mean_zero_equality_same_ground_mode (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r
      (DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)) v)
    (hmean : ∀s : ℝ,cotMean p u s=0)
    (heq : (∫s,cotDeviationEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    ∃a : (ℝ ∙ (p : E))ᗮ,∀x : sphere (0 : E) 1,u x=transverseMode (p : E) (a : E) v x := by
  obtain ⟨a,ha⟩ := cot_deviation_energy_equality_exists_linear hn p u r
    (cot_transverse_equality_reduced hn p u r heq).1 0
  let A : (ℝ ∙ (p : E))ᗮ := (cotScalarGround v 0)⁻¹ • a
  have hRatio := cot_transverse_equality_ground_ratio hn p u r v hv hpos heig heq
  have hShape : ∀y : PolarDir p,∀s : ℝ,cotDeviation p u (y,s)=cotScalarGround v s*⟪A,(y : (ℝ ∙ (p : E))ᗮ)⟫_ℝ := by
    intro y s
    rw [hRatio y s,ha y]
    simp only [A,real_inner_smul_left]
    ring
  have hCot : ∀q : PolarDir p × ℝ,u (cotSpherePD (n := n) p q)=
      transverseMode (p : E) (A : E) v (cotSpherePD (n := n) p q) := by
    intro q
    have hdev : cotDeviation p u q=u (cotSpherePD (n := n) p q) := by
      change u (cotSpherePD (n := n) p q)-cotMean p u q.2=_
      rw [hmean q.2,sub_zero]
    rw [←hdev,hShape q.1 q.2]
    unfold transverseMode
    rw [cot_complement_coordinate,cotSpherePD_height]
    unfold cotScalarGround cotHeight
    ring
  have hfun := cot_continuous_sphere_eq p u
    (transverseMode (p : E) (A : E) v) u.contMDiff.continuous
    (transverseMode_contMDiff (n := n+1) (p : E) (A : E) v hv).continuous hCot
  exact ⟨A,congrFun hfun⟩

/-- A single original positive normalized ground profile and one axis-
orthogonal vector represent the entire actual equality state. The profile
existence, its norm and its original auxiliary ODE are all proved. -/
theorem cot_transverse_mean_zero_equality_exists_sphere_mode (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (hmean : ∀s : ℝ,cotMean p u s=0)
    (heq : (∫s,cotDeviationEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    ∃(v : ℝ → ℝ) (a : (ℝ ∙ (p : E))ᗮ),ContDiff ℝ 2 v ∧
      (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧ DFL.Spectral.latitudeNorm (n+3) r v=1 ∧
      DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r
        (DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)) v ∧
      ∀x : sphere (0 : E) 1,u x=transverseMode (p : E) (a : E) v x := by
  obtain ⟨v,hv,hpos,hN,heig⟩ := DFL.Spectral.original_first_transverse_weighted_ground_exists (n+1) r
  obtain ⟨a,ha⟩ := cot_transverse_mean_zero_equality_same_ground_mode hn p u r v hv hpos heig hmean heq
  exact ⟨v,a,hv,hpos,hN,heig,ha⟩

end DFLCotSphere
