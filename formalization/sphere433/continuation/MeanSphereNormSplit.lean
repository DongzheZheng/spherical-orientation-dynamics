import continuation.MeanSphereDomain

/-! Original weighted mean and norm orthogonality for the actual
whole-sphere angular average. All integrals use the proved round volume. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DFLCotSphere DFLAngularMean
namespace DFLMeanSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def sphereWeightedMean (p : sphere (0 : E) 1) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) : ℝ :=
  ∫x,Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*f x
    ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))
def sphereWeightedMass (p : sphere (0 : E) 1) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) : ℝ :=
  sphereWeightedMean (n := n) p r (fun x => (f x)^2)

private theorem weighted_integrable (p : sphere (0 : E) 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : Continuous f) :
    Integrable (fun x : sphere (0 : E) 1 => Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*f x)
      (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))) := by
  let : IsFiniteMeasure (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hw : Continuous (fun x : sphere (0 : E) 1 => Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)) :=
    Real.continuous_exp.comp (continuous_const.mul ((innerSL ℝ (p : E)).continuous.comp continuous_subtype_val))
  exact (hw.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+2)] in
private theorem polarNonempty (p : sphere (0 : E) 1) (hn : finrank ℝ E=n+2) : Nonempty (PolarDir p) := by
  let : Fact (finrank ℝ E=n+2) := ⟨hn⟩
  let : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1) :
    (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1).Nonempty)
  exact ⟨⟨y,hy⟩⟩

/-- The actual radial projection preserves the original physical weighted
mean, including the true poles. -/
theorem meanSphereProfile_weighted_mean (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (hvs : ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    sphereWeightedMean (n := n) p r (meanSphereProfile p v)=sphereWeightedMean (n := n) p r u := by
  let _ : Nonempty (PolarDir p) := polarNonempty p (Fact.out : finrank ℝ E=n+2)
  unfold sphereWeightedMean
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _
    (meanSphereProfile_contMDiff (n := n) p v hv).continuous,cot_weighted_mean_projection p r u]
  apply integral_congr_ae
  filter_upwards [] with s
  simp_rw [meanSphereProfile_cot p u v hvs]
  rw [integral_const,smul_eq_mul]
  unfold angularVolume
  ring

/-- The actual whole-sphere angular deviation has zero original physical
weighted mean for every input state, without assuming the input mean zero. -/
theorem meanSphereProfile_deviation_weighted_mean (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (hvs : ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    sphereWeightedMean (n := n) p r (fun x => u x-meanSphereProfile p v x)=0 := by
  have hA := (meanSphereProfile_contMDiff (n := n) p v hv).continuous
  unfold sphereWeightedMean
  simp_rw [mul_sub]
  rw [integral_sub (weighted_integrable (n := n) p r u u.contMDiff.continuous)
    (weighted_integrable (n := n) p r _ hA)]
  change sphereWeightedMean (n := n) p r u-sphereWeightedMean (n := n) p r (meanSphereProfile p v)=0
  rw [meanSphereProfile_weighted_mean p r u v hv hvs,sub_self]

/-- Genuine weighted L² orthogonality of the actual radial mean and its
actual angular complement. -/
theorem meanSphereProfile_deviation_weighted_orthogonal (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (hvs : ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    sphereWeightedMean (n := n) p r (fun x => meanSphereProfile p v x*(u x-meanSphereProfile p v x))=0 := by
  have hA := (meanSphereProfile_contMDiff (n := n) p v hv).continuous
  unfold sphereWeightedMean
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r
    (fun x => meanSphereProfile p v x*(u x-meanSphereProfile p v x))
    (hA.mul (u.contMDiff.continuous.sub hA))]
  have hh : ∀s : ℝ, (∫y : PolarDir p,
      cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*
        (meanSphereProfile p v (cotSpherePD (n := n) p (y,s))*
          (u (cotSpherePD (n := n) p (y,s))-meanSphereProfile p v (cotSpherePD (n := n) p (y,s))))
      ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p) (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)))=0 := by
    intro s
    simp_rw [meanSphereProfile_cot p u v hvs]
    change (∫y : PolarDir p,
      cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*
        (cotMean p u s*cotDeviation p u (y,s)) ∂riemannianVolumeMeasure (𝓡 n)
          (PolarDir p) (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)))=0
    simp_rw [← mul_assoc]
    rw [integral_const_mul,cotDeviation_mean_zero,mul_zero]
  simp only [hh,integral_zero]

/-- The original actual weighted mass splits into the two actual
whole-sphere form-domain states. -/
theorem meanSphereProfile_weighted_mass_split (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (hvs : ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    sphereWeightedMass (n := n) p r u=sphereWeightedMass (n := n) p r (meanSphereProfile p v)+
      sphereWeightedMass (n := n) p r (fun x => u x-meanSphereProfile p v x) := by
  have hA := (meanSphereProfile_contMDiff (n := n) p v hv).continuous
  have hD := u.contMDiff.continuous.sub hA
  have hID := weighted_integrable (n := n) p r _ (hD.pow 2)
  have hIA := weighted_integrable (n := n) p r _ (hA.pow 2)
  have hIX := weighted_integrable (n := n) p r _ (hA.mul hD)
  change Integrable (fun x : sphere (0 : E) 1 =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x-meanSphereProfile p v x)^2) _ at hID
  change Integrable (fun x : sphere (0 : E) 1 =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(meanSphereProfile p v x)^2) _ at hIA
  change Integrable (fun x : sphere (0 : E) 1 =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(meanSphereProfile p v x*(u x-meanSphereProfile p v x))) _ at hIX
  have hIS : Integrable (fun x : sphere (0 : E) 1 =>
      Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(meanSphereProfile p v x)^2+
      Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x-meanSphereProfile p v x)^2)
      (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))) := hIA.add hID
  have hpnt (x : sphere (0 : E) 1) : Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x)^2=
      Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(meanSphereProfile p v x)^2+
      Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x-meanSphereProfile p v x)^2+
      2*(Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(meanSphereProfile p v x*(u x-meanSphereProfile p v x))) := by ring
  unfold sphereWeightedMass sphereWeightedMean
  simp_rw [hpnt]
  rw [integral_add hIS (hIX.const_mul 2),integral_add hIA hID,integral_const_mul]
  have hx := meanSphereProfile_deviation_weighted_orthogonal p r u v hv hvs
  unfold sphereWeightedMean at hx
  rw [hx,mul_zero,add_zero]

end DFLMeanSphere
