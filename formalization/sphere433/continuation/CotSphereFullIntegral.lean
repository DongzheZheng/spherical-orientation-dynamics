import continuation.CotSphereVolume
import continuation.SeparatedMeasureFubini
import DifferentialGeometry.Analysis.Integration.Measure.NullImage
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! The two excluded poles have zero actual round volume. Consequently,
the original proved cot coordinate change of variables applies to the
whole sphere, including its genuine nonnegative integral disintegration. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry
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

/-- Every point has zero actual volume on the genuine positive-dimensional
round sphere. This follows from a smooth image of a null model singleton. -/
theorem round_sphere_singleton_volume_zero (x : sphere (0 : E) 1) :
    riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1)) {x} = 0 := by
  let V := EuclideanSpace ℝ (Fin (n+1))
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hzero : modelHaar (E := V) ({0} : Set V) = 0 := by
    simp
  have h := riemannianVolumeMeasure_image_eq_zero_of_mdifferentiableOn
    (roundMetric (E := E) (n := n+1))
    (f := fun _ : V => x) (s := ({0} : Set V)) mdifferentiableOn_const hzero
  simpa only [image_singleton] using h

/-- Both actual physical poles have zero actual round volume. -/
theorem round_sphere_poles_volume_zero (p : sphere (0 : E) 1) :
    riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1)) ({p} ∪ {-p}) = 0 := by
  exact measure_union_null (round_sphere_singleton_volume_zero (n := n) p)
    (round_sphere_singleton_volume_zero (n := n) (-p))

theorem round_sphere_polar_complement_volume_zero (p : sphere (0 : E) 1) :
    riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1)) (polarTarget p)ᶜ = 0 := by
  have hs : (polarTarget p)ᶜ = ({p} ∪ {-p}) := by
    ext x
    simp only [polarTarget,mem_compl_iff,mem_ofPred_eq,not_and_or,not_not,
      mem_union,mem_singleton_iff]
  rw [hs]
  exact round_sphere_poles_volume_zero p

/-- Deleting the two poles leaves the actual round measure unchanged. -/
theorem round_sphere_restrict_polarTarget (p : sphere (0 : E) 1) :
    (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))).restrict (polarTarget p) =
    riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1)) := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr (round_sphere_polar_complement_volume_zero p)

/-- Actual round volume on the entire sphere is the pushforward of the
actual cot pullback volume; the deleted poles are proved null. -/
theorem cotProductMetric_volume_pushforward_full (p : sphere (0 : E) 1) :
    Measure.map (cotSpherePD (n := n) p : PolarDir p × ℝ → sphere (0 : E) 1)
      (riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
        (cotProductMetric (n := n) p)) =
      riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1)) := by
  rw [cotProductMetric_volume_pushforward,round_sphere_restrict_polarTarget]

/-- Complete change of variables to actual round measure on the whole
sphere, without a pole-nullness premise. -/
theorem cot_sphere_volume_change_of_variables_full (p : sphere (0 : E) 1) :
    Measure.map (cotSpherePD (n := n) p : PolarDir p × ℝ → sphere (0 : E) 1)
      ((cotProductReferenceMeasure (n := n) p).withDensity
        (fun q => ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2))) =
      riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1)) := by
  rw [cot_sphere_volume_change_of_variables,round_sphere_restrict_polarTarget]

/-- Every measurable nonnegative observable on the entire physical sphere
has the genuine cot-coordinate integral with the derived density. -/
theorem cot_sphere_lintegral (p : sphere (0 : E) 1) (F : sphere (0 : E) 1 → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F x ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) =
      ∫⁻ q, ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2)*
        F (cotSpherePD (n := n) p q) ∂cotProductReferenceMeasure (n := n) p := by
  have hphi := (cotSpherePD_smooth (n := n) p).continuous.measurable
  have hd : Measurable (fun q : PolarDir p × ℝ =>
      ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2)) :=
    (ENNReal.continuous_ofReal.comp
      (((cotAngularScale_smooth.continuous.comp continuous_snd).pow n).mul
        (cotLineScale_smooth.continuous.comp continuous_snd))).measurable
  rw [← cot_sphere_volume_change_of_variables_full (n := n) p,lintegral_map hF hphi]
  simpa only [Pi.mul_apply,Function.comp_def] using
    lintegral_withDensity_eq_lintegral_mul _ hd (hF.comp hphi)

/-- Actual whole-sphere angular/longitudinal Tonelli formula, in the
manuscript's cot coordinates, for every continuous nonnegative observable. -/
theorem cot_sphere_lintegral_continuous (p : sphere (0 : E) 1)
    (F : sphere (0 : E) 1 → ℝ≥0∞) (hF : Continuous F) :
    (∫⁻ x, F x ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) =
      ∫⁻ s : ℝ, ∫⁻ y : PolarDir p,
        ENNReal.ofReal (cotAngularScale s^n*cotLineScale s)*
          F (cotSpherePD (n := n) p (y,s))
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := by
  rw [← cotProductMetric_volume_pushforward_full (n := n) p,
    lintegral_map hF.measurable (cotSpherePD_smooth (n := n) p).continuous.measurable]
  simpa only [finrank_euclideanSpace,Fintype.card_fin] using
    DFLSeparatedFubini.separated_lintegral
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      cotAngularScale_smooth.continuous cotLineScale_smooth.continuous
      (cotProductMetric_separated p) (fun q => F (cotSpherePD (n := n) p q))
      (hF.comp (cotSpherePD_smooth (n := n) p).continuous)

/-- The original axial Boltzmann weight on the actual whole sphere has
the explicit cot-coordinate factor exp(r*s/sqrt(1+s²)). -/
theorem cot_sphere_lintegral_axial_weight (p : sphere (0 : E) 1) (r : ℝ)
    (F : sphere (0 : E) 1 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))*F x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫⁻ q, ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2)*
        ENNReal.ofReal (Real.exp (r*(q.2*cotAngularScale q.2)))*
          F (cotSpherePD (n := n) p q) ∂cotProductReferenceMeasure (n := n) p := by
  have hw : Continuous (fun x : sphere (0 : E) 1 =>
      ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.inner continuous_subtype_val)))
  simpa only [cotSpherePD_height,mul_assoc] using
    cot_sphere_lintegral (n := n) p (fun x =>
      ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))*F x) (hw.measurable.mul hF)

/-- Actual angular/longitudinal Tonelli formula with the original physical
axial Boltzmann weight, for every continuous nonnegative observable. -/
theorem cot_sphere_lintegral_axial_weight_continuous (p : sphere (0 : E) 1) (r : ℝ)
    (F : sphere (0 : E) 1 → ℝ≥0∞) (hF : Continuous F) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))*F x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫⁻ s : ℝ, ∫⁻ y : PolarDir p,
        ENNReal.ofReal (cotAngularScale s^n*cotLineScale s)*
          ENNReal.ofReal (Real.exp (r*(s*cotAngularScale s)))*
            F (cotSpherePD (n := n) p (y,s))
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := by
  have hw : Continuous (fun x : sphere (0 : E) 1 =>
      ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.inner continuous_subtype_val)))
  simpa only [cotSpherePD_height,mul_assoc] using
    cot_sphere_lintegral_continuous (n := n) p (fun x =>
      ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))*F x)
      (hw.ennreal_mul hF (by intro x; left; positivity) (by intro x; right; simp))

end DFLCotSphere
