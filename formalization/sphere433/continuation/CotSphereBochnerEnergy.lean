import continuation.CotSphereFullIntegral
import continuation.CotSphereEnergy
import continuation.SeparatedBochnerFubini

/-! Actual full-sphere real integrals and the original weighted norm and
Dirichlet energy in angular/latitude coordinates. Pole nullness, volume
change of variables and gradient transformation are all proved upstream. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)] [FiniteDimensional ℝ E]

private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p × ℝ) := borel (PolarDir p × ℝ)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p × ℝ) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- True angular/latitude real Fubini for every continuous observable on
the whole sphere; integrability follows from compactness. -/
theorem cot_sphere_integral_continuous (p : sphere (0 : E) 1)
    (F : sphere (0 : E) 1 → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, ∫ y : PolarDir p,
        cotAngularScale s^n*cotLineScale s*F (cotSpherePD (n := n) p (y,s))
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := by
  let _ : IsFiniteMeasure (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
    (roundMetric (E := E) (n := n+1))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hI : Integrable F (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hphi := (cotSpherePD_smooth (n := n) p).continuous.measurable
  have hIm : Integrable F (Measure.map (cotSpherePD (n := n) p)
      (riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
        (cotProductMetric (n := n) p))) := by
    rw [cotProductMetric_volume_pushforward_full]
    exact hI
  have hIp := hIm.comp_aemeasurable hphi.aemeasurable
  rw [← cotProductMetric_volume_pushforward_full (n := n) p,
    integral_map hphi.aemeasurable hIm.aestronglyMeasurable]
  simpa only [finrank_euclideanSpace,Fintype.card_fin,Function.comp_def] using
    DFLSeparatedBochner.separated_integral
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      cotAngularScale_smooth.continuous cotLineScale_smooth.continuous
      (cotProductMetric_separated p) (F ∘ cotSpherePD (n := n) p) hIp

/-- Actual full-sphere integral with the original physical axial weight,
with its explicit angular/latitude density. -/
theorem cot_sphere_integral_axial_weight_continuous (p : sphere (0 : E) 1) (r : ℝ)
    (F : sphere (0 : E) 1 → ℝ) (hF : Continuous F) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*F x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, ∫ y : PolarDir p,
        cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*
          F (cotSpherePD (n := n) p (y,s))
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := by
  have hw : Continuous (fun x : sphere (0 : E) 1 =>
      Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)) :=
    Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.inner continuous_subtype_val))
  simpa only [cotSpherePD_height,mul_assoc] using
    cot_sphere_integral_continuous (n := n) p
      (fun x => Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*F x) (hw.mul hF)

/-- The actual weighted norm of a smooth full-sphere state, including
both poles, in the original angular/latitude coordinates. -/
theorem cot_sphere_weighted_norm (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x)^2
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, ∫ y : PolarDir p,
        cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*
          (u (cotSpherePD (n := n) p (y,s)))^2
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume :=
  cot_sphere_integral_axial_weight_continuous (n := n) p r _ (u.contMDiff.continuous.pow 2)

/-- The actual original weighted Dirichlet form, decomposed into genuine
angular slice energy and the ordinary latitude derivative energy. -/
theorem cot_sphere_weighted_energy (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, ∫ y : PolarDir p,
        cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*
          ((cotAngularScale s^2)⁻¹*
            normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
              (fun z : PolarDir p => u (cotSpherePD (n := n) p (z,s))) y+
            (cotLineScale s^2)⁻¹*
              (deriv (fun t : ℝ => u (cotSpherePD (n := n) p (y,t))) s)^2)
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := by
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _
    (normGradSqFun_continuous _ u.contMDiff)]
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [] with y
  rw [cotSpherePD_gradient_energy (n := n) p u (y,s)]

end DFLCotSphere
