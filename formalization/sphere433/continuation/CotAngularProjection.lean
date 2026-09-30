import continuation.SeparatedMeanEnergy
import continuation.CotSphereBochnerEnergy

/-! Genuine angular mean projection and orthogonal norm/Dirichlet splits
for arbitrary smooth states of the actual full physical sphere. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLAngularMean
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)] [FiniteDimensional ℝ E]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
omit [FiniteDimensional ℝ E] in
private theorem polarNonempty (n : ℕ) [Fact (finrank ℝ E = n+2)] (p : sphere (0 : E) 1) : Nonempty (PolarDir p) := by
  let : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1) :
    (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1).Nonempty)
  exact ⟨⟨y,hy⟩⟩

def cotMean (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) : ℝ → ℝ :=
  angularMean (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotSpherePullback p u)

def cotDeviation (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮(𝓡 n).prod 𝓘(ℝ, ℝ), PolarDir p × ℝ; ℝ⟯ :=
  angularDeviation (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotSpherePullback p u)

theorem cotMean_smooth (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) : ContDiff ℝ ∞ (cotMean p u) :=
  angularMean_smooth _ _

theorem cotDeviation_mean_zero (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ) :
    (∫ y : PolarDir p, cotDeviation p u (y,s)
      ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))) = 0 :=
  by
    let _ : Nonempty (PolarDir p) := polarNonempty n p
    exact angularDeviation_mean_zero _ _ s

/-- The actual full-sphere physical weighted mean is the radial mean
of the genuine angular projection. -/
theorem cot_weighted_mean_projection (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*u x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        (angularVolume (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))*cotMean p u s) := by
  let _ : Nonempty (PolarDir p) := polarNonempty n p
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r u u.contMDiff.continuous]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_const_mul]
  congr 1
  exact (mul_div_cancel₀ _ (ne_of_gt (angularVolume_pos
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))))).symm

/-- Original full-sphere norm splitting into the radial angular mean and
its genuinely mean-zero angular complement. -/
theorem cot_weighted_norm_projection (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x)^2
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        (angularVolume (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))*(cotMean p u s)^2+
          ∫ y : PolarDir p, (cotDeviation p u (y,s))^2
            ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
              (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))) := by
  let _ : Nonempty (PolarDir p) := polarNonempty n p
  rw [cot_sphere_weighted_norm (n := n) p r u]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_const_mul]
  congr 1
  exact angular_square_split _ (cotSpherePullback p u) s

/-- Actual full-sphere energy equals the actual product-gradient energy
before splitting its radial and angular projections. -/
theorem cot_weighted_energy_product (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
          (cotSpherePullback p u) (y,s)
            ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
              (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) := by
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _
    (normGradSqFun_continuous _ u.contMDiff)]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [cotSpherePD_normGradSq]

/-- Original orthogonal radial/angular Dirichlet split for every smooth
full-sphere state, using the actual projection and all physical weights. -/
theorem cot_weighted_energy_projection (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ((cotAngularScale s^2)⁻¹*
          (∫ y : PolarDir p, normGradSqFun
            (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
              (fun z : PolarDir p => cotDeviation p u (z,s)) y
            ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
              (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)))+
          (cotLineScale s^2)⁻¹*
            (angularVolume (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))*(deriv (cotMean p u) s)^2+
              ∫ y : PolarDir p, (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2
                ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
                  (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)))) := by
  let _ : Nonempty (PolarDir p) := polarNonempty n p
  rw [cot_weighted_energy_product p r u]
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  exact DFLSeparatedMean.separated_angular_mean_energy
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    (cotProductMetric_separated p) (cotSpherePullback p u) s

end DFLCotSphere
