import continuation.CotSphereFullIntegral
import DFLSphere433.OriginalLatitude.AngularComparison
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! True cot-to-latitude substitution and the original one-dimensional
latitude density. The exponent is fixed by the actual sphere dimension,
including the singular but integrable latitude endpoints. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
namespace DFLCotSphere

def cotHeight (s : ℝ) : ℝ := s*cotAngularScale s

theorem cotHeight_cos (s : ℝ) : cotHeight s = Real.cos (cotAngle s) :=
  (cotAngle_cos s).symm

theorem cotLineScale_eq_square (s : ℝ) : cotLineScale s = cotAngularScale s^2 := by
  unfold cotLineScale cotAngularScale
  rw [inv_pow,Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)]

theorem cotHeight_w (s : ℝ) : 1-cotHeight s^2 = cotAngularScale s^2 := by
  have h := Real.sin_sq_add_cos_sq (cotAngle s)
  rw [cotAngle_sin,← cotHeight_cos] at h
  linarith

theorem cotHeight_smooth : ContDiff ℝ ∞ cotHeight := contDiff_id.mul cotAngularScale_smooth

theorem cotHeight_hasDerivAt (s : ℝ) : HasDerivAt cotHeight (cotAngularScale s^3) s := by
  have h := (Real.hasDerivAt_cos (cotAngle s)).comp s (cotAngle_hasDerivAt s)
  have he : Real.cos ∘ cotAngle = cotHeight := funext cotAngle_cos
  rw [he] at h
  convert! h using 1
  rw [cotAngle_sin,cotLineScale_eq_square]
  ring

theorem cotHeight_strictMono : StrictMono cotHeight := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(cotHeight_hasDerivAt s).deriv]
  exact pow_pos (cotAngularScale_pos s) 3

theorem cotHeight_mem (s : ℝ) : cotHeight s ∈ Ioo (-1 : ℝ) 1 := by
  rw [cotHeight_cos]
  exact Real.mapsTo_cos_Ioo (cotAngle_mem s)

theorem cotHeight_range : range cotHeight = Ioo (-1 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨s,rfl⟩
    exact cotHeight_mem s
  · intro ht
    refine ⟨cotParameter (Real.arccos t),?_⟩
    rw [cotHeight_cos,cotAngle_cotParameter
      ⟨Real.arccos_pos.mpr ht.2,Real.arccos_lt_pi.mpr ht.1⟩,
      Real.cos_arccos ht.1.le ht.2.le]

/-- The actual Jacobian exactly converts the cot density to the original
latitude weight on the genuine sphere of dimension n+1. -/
theorem cot_latitude_density (n : ℕ) (r s : ℝ) :
    cotAngularScale s^3 * DFL.Spectral.radialWeight (n+1) r (cotHeight s) =
      Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s) := by
  have hf := cotAngularScale_pos s
  have hp : Real.rpow (cotAngularScale s^2) ((((n+1 : ℕ) : ℝ)-2)/2) *
      cotAngularScale s^3 = cotAngularScale s^n*cotLineScale s := by
    rw [cotLineScale_eq_square]
    simp only [Real.rpow_eq_pow]
    calc
      _ = (cotAngularScale s) ^
          (2*((((n+1 : ℕ) : ℝ)-2)/2)) * cotAngularScale s^3 := by
        rw [← Real.rpow_two,← Real.rpow_mul hf.le]
      _ = (cotAngularScale s) ^
          (2*((((n+1 : ℕ) : ℝ)-2)/2)+3) := by
        rw [← Real.rpow_natCast (cotAngularScale s) 3,← Real.rpow_add hf]
        norm_num
      _ = (cotAngularScale s) ^ ((n : ℝ)+2) := by
        congr 1
        push_cast
        ring
      _ = _ := by rw [Real.rpow_add hf,Real.rpow_natCast,Real.rpow_two]
  unfold DFL.Spectral.radialWeight
  rw [cotHeight_w]
  linear_combination Real.exp (r*cotHeight s)*hp

/-- Genuine one-variable change of variables from the entire cot line to
the original open latitude interval, with the exact original weight. -/
theorem cot_latitude_lintegral (n : ℕ) (r : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ s : ℝ, ENNReal.ofReal
      (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s))*G (cotHeight s)) =
      ∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (DFL.Spectral.radialWeight (n+1) r t)*G t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun s _ => (cotHeight_hasDerivAt s).hasDerivWithinAt)
    cotHeight_strictMono.injective.injOn
    (fun t => ENNReal.ofReal (DFL.Spectral.radialWeight (n+1) r t)*G t)
  simp only [image_univ,cotHeight_range,Measure.restrict_univ,
    abs_of_pos (pow_pos (cotAngularScale_pos _) 3)] at h
  have he : (fun s : ℝ => ENNReal.ofReal (cotAngularScale s^3)*
      (ENNReal.ofReal (DFL.Spectral.radialWeight (n+1) r (cotHeight s))*G (cotHeight s))) =
      (fun s : ℝ => ENNReal.ofReal
        (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s))*G (cotHeight s)) := by
    funext s
    rw [← mul_assoc,← ENNReal.ofReal_mul (pow_pos (cotAngularScale_pos s) 3).le,
      cot_latitude_density]
  rw [he] at h
  exact h.symm

/-- The same actual scalar substitution for real-valued integrals, derived
from the genuine differentiable injective Jacobian theorem. -/
theorem cot_latitude_integral (n : ℕ) (r : ℝ) (G : ℝ → ℝ) :
    (∫ s : ℝ, Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s)*G (cotHeight s)) =
      ∫ t in Ioo (-1 : ℝ) 1, DFL.Spectral.radialWeight (n+1) r t*G t := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun s _ => (cotHeight_hasDerivAt s).hasDerivWithinAt)
    cotHeight_strictMono.injective.injOn (fun t => DFL.Spectral.radialWeight (n+1) r t*G t)
  simp only [image_univ,cotHeight_range,Measure.restrict_univ,
    abs_of_pos (pow_pos (cotAngularScale_pos _) 3),smul_eq_mul] at h
  simp_rw [← mul_assoc,cot_latitude_density] at h
  exact h.symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)] [FiniteDimensional ℝ E]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The genuine angular round-sphere total mass, retaining the actual
geometric normalization of the original latitude disintegration. -/
def angularRoundMass (p : sphere (0 : E) 1) : ℝ≥0∞ :=
  riemannianVolumeMeasure (𝓡 n) (PolarDir p)
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) univ

/-- The actual whole-round-sphere latitude marginal with the physical
exponential weight is exactly the original radialWeight, multiplied by
the actual angular round-sphere mass. No marginal formula is an input. -/
theorem round_sphere_weighted_latitude_lintegral (p : sphere (0 : E) 1) (r : ℝ)
    (G : ℝ → ℝ≥0∞) (hG : Continuous G) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (r*⟪(p : E),(x : E)⟫_ℝ))*G ⟪(p : E),(x : E)⟫_ℝ
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      angularRoundMass (n := n) p *
        ∫⁻ t in Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (DFL.Spectral.radialWeight (n+1) r t)*G t := by
  have hM := cot_sphere_lintegral_axial_weight_continuous (n := n) p r
    (fun x => G ⟪(p : E),(x : E)⟫_ℝ)
    (hG.comp (continuous_const.inner continuous_subtype_val))
  simp only [cotSpherePD_height] at hM
  have hw : Continuous (fun s : ℝ =>
      Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s)) :=
    (Real.continuous_exp.comp (continuous_const.mul cotHeight_smooth.continuous)).mul
      ((cotAngularScale_smooth.continuous.pow n).mul cotLineScale_smooth.continuous)
  have hW : Measurable (fun s : ℝ => ENNReal.ofReal
      (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s))*G (cotHeight s)) :=
    (ENNReal.continuous_ofReal.comp hw).measurable.mul
      (hG.measurable.comp cotHeight_smooth.continuous.measurable)
  calc
    _ = ∫⁻ s : ℝ, ∫⁻ _ : PolarDir p,
        ENNReal.ofReal (cotAngularScale s^n*cotLineScale s)*
          ENNReal.ofReal (Real.exp (r*(s*cotAngularScale s)))*G (s*cotAngularScale s)
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := hM
    _ = ∫⁻ s : ℝ, (ENNReal.ofReal
        (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s))*G (cotHeight s))*
          angularRoundMass (n := n) p := by
      apply lintegral_congr
      intro s
      rw [lintegral_const]
      change (ENNReal.ofReal (cotAngularScale s^n*cotLineScale s)*
        ENNReal.ofReal (Real.exp (r*cotHeight s))*G (cotHeight s))*_ = _
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    _ = (∫⁻ s : ℝ, ENNReal.ofReal
        (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s))*G (cotHeight s))*
          angularRoundMass (n := n) p := lintegral_mul_const _ hW
    _ = _ := by rw [cot_latitude_lintegral,mul_comm]

end DFLCotSphere
