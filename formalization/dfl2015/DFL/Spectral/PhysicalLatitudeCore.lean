import DFL.Spectral.CoreCoordinate
import DFL.Spectral.GroundMoments
import DFL.Geometry.SuccLawFull
import DFL.Geometry.MomentBridgeSucc

/-!
# Exact original-sphere latitude restriction of the Dirichlet form

This implements the radial smooth-core step of the manuscript's
decomposition: the genuine spherical tangent gradient and the genuine
vMF measure give exactly the stated latitude weight. It does not claim
density of radial tests in the entire sphere form or angular Parseval.
-/

namespace DFL.Spectral

open MeasureTheory InnerProductSpace Set
open scoped Interval

noncomputable section

def latitudeCore (d : ℕ) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) : SphereC1Core d :=
  ⟨fun x => v (x 0), hv.comp (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := 0) (n := 1))⟩

theorem latitudeCore_value (d : ℕ) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v)
    (x : SpherePoint d) :
    coreValue d (latitudeCore d v hv) x = v (fieldCoordinate d x) := rfl

private theorem latitude_ambient_gradient (d : ℕ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (x : Ambient d) :
    gradient (fun y : Ambient d => v (y 0)) x =
      deriv v (x 0) • EuclideanSpace.single 0 (1 : ℝ) := by
  have hvd := hv.differentiable (by norm_num)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt (x := x)
  have hder : HasFDerivAt (fun y : Ambient d => v (y 0))
      (deriv v (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))) x := by
    convert ((hvd (x 0)).hasDerivAt.hasFDerivAt).comp x hcoord using 1
    ext z
    simp
    ring
  have hdual : toDual ℝ (Ambient d) (EuclideanSpace.single 0 (1 : ℝ)) =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) := by
    ext z
    simpa using EuclideanSpace.inner_single_left 0 (1 : ℝ) z
  have hdual' : toDual ℝ (Ambient d) (deriv v (x 0) • EuclideanSpace.single 0 (1 : ℝ)) =
      deriv v (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1)) := by
    rw [map_smul, hdual]
  exact (hasGradientAt_iff_hasFDerivAt.mpr (hdual' ▸ hder)).gradient

theorem latitudeCore_tangentGradient (d : ℕ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (x : SpherePoint d) :
    coreTangentGradient d (latitudeCore d v hv) x =
      deriv v (fieldCoordinate d x) • coordinateTangentGradient d 0 x := by
  unfold coreTangentGradient latitudeCore
  rw [latitude_ambient_gradient d v hv]
  have he : inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x.1 = x.1 0 := by
    simpa using EuclideanSpace.inner_single_left 0 (1 : ℝ) x.1
  simp only [real_inner_smul_left, he, coordinateTangentGradient,
    fieldCoordinate, sphereCoordinate, smul_sub, smul_smul]

theorem latitudeCore_energy_pointwise (d : ℕ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (x : SpherePoint d) :
    ‖coreTangentGradient d (latitudeCore d v hv) x‖ ^ 2 =
      (1 - (fieldCoordinate d x) ^ 2) * (deriv v (fieldCoordinate d x)) ^ 2 := by
  rw [latitudeCore_tangentGradient, norm_smul, mul_pow,
    coordinateTangentGradient_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs, fieldCoordinate, sphereCoordinate]
  ring

private theorem spectral_beta_weight (k : ℕ) (r t : ℝ)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    radialWeight (k + 2) r t = Real.exp (r * t) * DFL.Geometry.betaPower k t := by
  have hw : 0 ≤ 1 - t ^ 2 := by
    rcases ht with ⟨hl, hr⟩
    nlinarith
  unfold radialWeight DFL.Geometry.betaPower
  have he : (((k + 2 : ℕ) : ℝ) - 2) / 2 = (k : ℝ) / 2 := by push_cast; ring
  rw [he, Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (k : ℝ) hw, Real.rpow_natCast]

private theorem surface_latitude_integral (k : ℕ) (r : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : SpherePoint (k + 2), Real.exp (r * fieldCoordinate (k + 2) x) *
      f (fieldCoordinate (k + 2) x) ∂surfaceMeasure (k + 2)) =
      DFL.Geometry.sphereBetaConst k *
        (∫ t in (-1 : ℝ)..1, radialWeight (k + 2) r t * f t) := by
  have hmap : (∫ x : SpherePoint (k + 2), Real.exp (r * fieldCoordinate (k + 2) x) *
      f (fieldCoordinate (k + 2) x) ∂surfaceMeasure (k + 2)) =
      ∫ t : ℝ, Real.exp (r * t) * f t ∂DFL.Geometry.coordinateLaw (k + 3) (by omega) := by
    symm
    exact integral_map_of_stronglyMeasurable
      (DFL.Geometry.continuous_coordinate (k + 3) (by omega)).measurable
      (show StronglyMeasurable (fun t : ℝ => Real.exp (r * t) * f t) from
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf).stronglyMeasurable)
  rw [hmap, DFL.Geometry.coordinateLaw_succ_eq_smul_beta,
    integral_smul_measure, ENNReal.toReal_ofReal (DFL.Geometry.sphereBetaConst_pos k).le]
  rw [DFL.Geometry.betaCoordinateMeasure_integral]
  simp only [smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htcc : t ∈ Icc (-1 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  dsimp only
  rw [spectral_beta_weight k r t htcc]
  ring

/-- The normalized original sphere latitude law, for every continuous
test and every physical dimension `d=k+2≥2`. No marginal law is assumed. -/
theorem aligned_latitude_integral (k : ℕ) (r : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : SpherePoint (k + 2), f (fieldCoordinate (k + 2) x) ∂alignedMeasure (k + 2) r) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k + 2) r t * f t) /
        (∫ t in (-1 : ℝ)..1, radialWeight (k + 2) r t) := by
  rw [alignedMeasure, integral_tilted]
  simp only [smul_eq_mul]
  have hquot : (∫ x : SpherePoint (k + 2),
      (Real.exp (r * fieldCoordinate (k + 2) x) /
        ∫ y : SpherePoint (k + 2), Real.exp (r * fieldCoordinate (k + 2) y) ∂surfaceMeasure (k + 2)) *
          f (fieldCoordinate (k + 2) x) ∂surfaceMeasure (k + 2)) =
      (∫ x : SpherePoint (k + 2), Real.exp (r * fieldCoordinate (k + 2) x) *
        f (fieldCoordinate (k + 2) x) ∂surfaceMeasure (k + 2)) /
        (∫ y : SpherePoint (k + 2), Real.exp (r * fieldCoordinate (k + 2) y) ∂surfaceMeasure (k + 2)) := by
    simp_rw [div_mul_eq_mul_div]
    exact integral_div _ _
  rw [hquot, surface_latitude_integral k r f hf]
  have hden := surface_latitude_integral k r (fun _ => 1) continuous_const
  simp only [mul_one] at hden
  rw [hden]
  exact mul_div_mul_left _ _ (ne_of_gt (DFL.Geometry.sphereBetaConst_pos k))

/-- The exact radial smooth-core Dirichlet energy derived from the
physical sphere's intrinsic tangent gradient and proved coordinate law. -/
theorem latitudeCore_energy_integral (k : ℕ) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) :
    coreEnergy (k + 2) r (latitudeCore (k + 2) v (hv.of_le (by norm_num))) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k + 2) r t *
        ((1 - t ^ 2) * (deriv v t) ^ 2)) /
      (∫ t in (-1 : ℝ)..1, radialWeight (k + 2) r t) := by
  unfold coreEnergy
  simp_rw [latitudeCore_energy_pointwise]
  have hd : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  exact aligned_latitude_integral k r (fun t => (1 - t ^ 2) * (deriv v t) ^ 2)
    ((continuous_const.sub (continuous_id.pow 2)).mul (hd.pow 2))

end

end DFL.Spectral
