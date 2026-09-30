import DFL.Spectral.ZeroFieldMoments

/-!
# An original-sphere coordinate trial calculation at zero field

This module computes the geometric tangential projection of a coordinate's
ambient gradient, its energy and its actual variance. The full `H¹` Rayleigh
infimum and spectral ordering are not defined by these trial calculations.
-/

namespace DFL.Spectral

open MeasureTheory Metric

noncomputable section

/-- Orthogonal projection of the ambient coordinate gradient `eᵢ` to the
tangent hyperplane of the actual sphere at `x`. -/
def coordinateTangentGradient (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) : Ambient d :=
  EuclideanSpace.single i (1 : ℝ) - sphereCoordinate d i x • x.1

theorem coordinateTangentGradient_tangent (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) :
    inner ℝ (coordinateTangentGradient d i x) x.1 = 0 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x.1 = x.1 i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x.1
  simp [coordinateTangentGradient, inner_sub_left, real_inner_smul_left,
    hx, sphereCoordinate, hsingle]

/-- On a tangent vector, this projection represents the directional
derivative of the restricted coordinate function. -/
theorem coordinateTangentGradient_pairing (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) (v : Ambient d) (hv : inner ℝ x.1 v = 0) :
    inner ℝ (coordinateTangentGradient d i x) v = v i := by
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ)) v = v i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) v
  simp [coordinateTangentGradient, inner_sub_left, real_inner_smul_left,
    hv, hsingle]

/-- The pointwise intrinsic energy of a coordinate is `1-xᵢ²`. -/
theorem coordinateTangentGradient_norm_sq (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) :
    ‖coordinateTangentGradient d i x‖ ^ 2 =
      1 - sphereCoordinate d i x ^ 2 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x.1 = x.1 i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x.1
  rw [coordinateTangentGradient, norm_sub_sq_real]
  simp [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    hx, sphereCoordinate, hsingle]
  ring

/-- The integrated geometric energy of any coordinate on the original
zero-field sphere. -/
theorem sphereCoordinate_tangent_energy_zero (d : ℕ) (i : Fin (d + 1)) :
    (∫ x, ‖coordinateTangentGradient d i x‖ ^ 2 ∂alignedMeasure d 0) =
      (d : ℝ) / (d + 1 : ℝ) := by
  simp_rw [coordinateTangentGradient_norm_sq d i]
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  rw [integral_sub (integrable_const 1) (sphereCoordinate_square_integrable d i)]
  rw [sphereCoordinate_square_mean_zero]
  simp
  field_simp
  all_goals ring

/-- The integrated coordinate trial energy on the original normalized
zero-field sphere is `d/(d+1)`. -/
theorem fieldCoordinate_tangent_energy_zero (d : ℕ) :
    (∫ x, ‖coordinateTangentGradient d 0 x‖ ^ 2 ∂alignedMeasure d 0) =
      (d : ℝ) / (d + 1 : ℝ) := by
  exact sphereCoordinate_tangent_energy_zero d 0

def sphereCoordinateTrialRatio (d : ℕ) (i : Fin (d + 1)) : ℝ :=
  (∫ x, ‖coordinateTangentGradient d i x‖ ^ 2 ∂alignedMeasure d 0) /
    sphereVariance d 0 (sphereCoordinate d i)

theorem sphereCoordinateTrialRatio_eq (d : ℕ) (i : Fin (d + 1)) :
    sphereCoordinateTrialRatio d i = d := by
  rw [sphereCoordinateTrialRatio, sphereCoordinate_tangent_energy_zero,
    sphereCoordinate_variance_zero]
  have h : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- A coordinate perpendicular to the distinguished field axis whenever
the physical sphere has dimension at least one. -/
def transverseIndex (d : ℕ) (hd : 0 < d) : Fin (d + 1) :=
  ⟨1, by omega⟩

theorem transverseCoordinateTrialRatio_eq (d : ℕ) (hd : 0 < d) :
    sphereCoordinateTrialRatio d (transverseIndex d hd) = d :=
  sphereCoordinateTrialRatio_eq d (transverseIndex d hd)

/-- Ratio of the explicitly computed coordinate tangent energy and the
original-sphere variance; this is a trial value, not the global infimum. -/
def fieldCoordinateTrialRatio (d : ℕ) : ℝ :=
  (∫ x, ‖coordinateTangentGradient d 0 x‖ ^ 2 ∂alignedMeasure d 0) /
    sphereVariance d 0 (fieldCoordinate d)

theorem fieldCoordinateTrialRatio_eq (d : ℕ) :
    fieldCoordinateTrialRatio d = d := by
  rw [fieldCoordinateTrialRatio, fieldCoordinate_tangent_energy_zero,
    fieldCoordinate_variance_zero]
  have h : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end

end DFL.Spectral
