import continuation.LatMeasureIdentity
import continuation.CotSphereBochnerEnergy
import DFLSphere433.OriginalLatitude.GroundMoments

/-! Actual real-valued round-sphere latitude marginal and the original
one-dimensional latitude norm. The common angular constant is the true
round angular-sphere total volume, not an assumed cone-measure identity. -/
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
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The actual angular round-sphere total volume, as a real scalar. -/
def angularRoundVolume (p : sphere (0 : E) 1) : ℝ := (angularRoundMass (n := n) p).toReal

/-- The genuine angular round total volume is strictly positive and
finite; nonempty angular geometry follows from its actual dimension. -/
theorem angularRoundVolume_pos (p : sphere (0 : E) 1) :
    0 < angularRoundVolume (n := n) p := by
  let : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  let _ : IsFiniteMeasure (riemannianVolumeMeasure (𝓡 n) (PolarDir p)
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  let _ : (riemannianVolumeMeasure (𝓡 n) (PolarDir p)
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure _
  have hs : (univ : Set (PolarDir p)).Nonempty := by
    rcases (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1) :
      (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1).Nonempty) with ⟨y,hy⟩
    exact ⟨⟨y,hy⟩,mem_univ _⟩
  apply ENNReal.toReal_pos
  · exact ne_of_gt (isOpen_univ.measure_pos _ hs)
  · exact measure_ne_top _ _

/-- The actual weighted round latitude marginal for every continuous
real observable, with its precise original radial weight. -/
theorem round_sphere_weighted_latitude_integral (p : sphere (0 : E) 1) (r : ℝ)
    (G : ℝ → ℝ) (hG : Continuous G) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*G ⟪(p : E),(x : E)⟫_ℝ
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      angularRoundVolume (n := n) p *
        ∫ t in Ioo (-1 : ℝ) 1, DFL.Spectral.radialWeight (n+1) r t*G t := by
  have hM := cot_sphere_integral_axial_weight_continuous (n := n) p r
    (fun x => G ⟪(p : E),(x : E)⟫_ℝ)
    (hG.comp (continuous_const.inner continuous_subtype_val))
  simp only [cotSpherePD_height] at hM
  calc
    _ = ∫ s : ℝ, ∫ _ : PolarDir p,
        cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))*G (s*cotAngularScale s)
        ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) ∂volume := hM
    _ = ∫ s : ℝ, angularRoundVolume (n := n) p *
        (Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s)*G (cotHeight s)) := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [integral_const]
      change (angularRoundMass (n := n) p).toReal *
        (cotAngularScale s^n*cotLineScale s*Real.exp (r*cotHeight s)*G (cotHeight s)) = _
      unfold angularRoundVolume
      ring
    _ = angularRoundVolume (n := n) p *
        (∫ s : ℝ, Real.exp (r*cotHeight s)*(cotAngularScale s^n*cotLineScale s)*G (cotHeight s)) :=
      integral_const_mul _ _
    _ = _ := by rw [cot_latitude_integral]

/-- The actual real latitude marginal in the original manuscript's
oriented interval-integral notation. Endpoints are Lebesgue null. -/
theorem round_sphere_weighted_latitude_intervalIntegral (p : sphere (0 : E) 1) (r : ℝ)
    (G : ℝ → ℝ) (hG : Continuous G) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*G ⟪(p : E),(x : E)⟫_ℝ
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      angularRoundVolume (n := n) p *
        ∫ t in (-1 : ℝ)..1, DFL.Spectral.radialWeight (n+1) r t*G t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  exact round_sphere_weighted_latitude_integral p r G hG

/-- The actual weighted spherical norm of a latitude profile is exactly
the original latitudeNorm times the genuine positive angular round volume. -/
theorem round_sphere_weighted_latitude_norm (p : sphere (0 : E) 1) (r : ℝ)
    (v : ℝ → ℝ) (hv : Continuous v) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(v ⟪(p : E),(x : E)⟫_ℝ)^2
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      angularRoundVolume (n := n) p * DFL.Spectral.latitudeNorm (n+1) r v :=
  round_sphere_weighted_latitude_intervalIntegral p r (fun t => (v t)^2) (hv.pow 2)

end DFLCotSphere
