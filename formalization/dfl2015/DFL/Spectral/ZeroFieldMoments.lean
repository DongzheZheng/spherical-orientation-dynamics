import DFL.Spectral.SphereOrthogonal
import DFL.Spectral.RayleighDenominator

/-!
# The coordinate moments of the original zero-field sphere
-/

namespace DFL.Spectral

open MeasureTheory Metric

noncomputable section

def sphereCoordinate (d : ℕ) (i : Fin (d + 1)) (x : SpherePoint d) : ℝ :=
  x.1 i

theorem sphereCoordinate_continuous (d : ℕ) (i : Fin (d + 1)) :
    Continuous (sphereCoordinate d i) := by
  unfold sphereCoordinate
  fun_prop

theorem sphereCoordinate_antipodal (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) :
    sphereCoordinate d i (antipodal d x) = -sphereCoordinate d i x := by
  simp [sphereCoordinate, antipodal]

theorem sphereCoordinate_surface_mean_zero (d : ℕ) (i : Fin (d + 1)) :
    ∫ x, sphereCoordinate d i x ∂surfaceMeasure d = 0 := by
  have h := (antipodal_measurePreserving d).integral_comp'
    (sphereCoordinate d i)
  have hneg : (∫ x, -sphereCoordinate d i x ∂surfaceMeasure d) =
      ∫ x, sphereCoordinate d i x ∂surfaceMeasure d := by
    simpa [antipodalMeasurableEquiv, sphereCoordinate_antipodal] using h
  rw [integral_neg] at hneg
  linarith

theorem sphereCoordinate_mean_zero (d : ℕ) (i : Fin (d + 1)) :
    ∫ x, sphereCoordinate d i x ∂alignedMeasure d 0 = 0 := by
  rw [alignedMeasure_zero, integral_smul_measure,
    sphereCoordinate_surface_mean_zero]
  simp

theorem sphereCoordinate_abs_le_one (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) : |sphereCoordinate d i x| ≤ 1 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  calc
    |sphereCoordinate d i x| = ‖sphereCoordinate d i x‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖(x.1 : Ambient d)‖ := PiLp.norm_apply_le x.1 i
    _ = 1 := hx

theorem sphereCoordinate_square_integrable (d : ℕ) (i : Fin (d + 1)) :
    Integrable (fun x => sphereCoordinate d i x ^ 2) (alignedMeasure d 0) := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  refine Integrable.of_bound ((sphereCoordinate_continuous d i).pow 2).aestronglyMeasurable
    1 ?_
  exact ae_of_all _ (fun x => by
    have hc := sphereCoordinate_abs_le_one d i x
    calc
      ‖sphereCoordinate d i x ^ 2‖ = |sphereCoordinate d i x| ^ 2 := by
        simp [norm_pow, Real.norm_eq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc _
      _ = 1 := by norm_num)

def coordinateSwap (d : ℕ) (i j : Fin (d + 1)) :
    Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem coordinateSwap_apply (d : ℕ) (i j : Fin (d + 1))
    (x : Ambient d) :
    (coordinateSwap d i j x) i = x j := by
  simp [coordinateSwap, Equiv.piCongrLeft'_apply]

theorem sphereCoordinate_swap (d : ℕ) (i j : Fin (d + 1))
    (x : SpherePoint d) :
    sphereCoordinate d i
      (sphereIsometry d (coordinateSwap d i j) x) = sphereCoordinate d j x := by
  exact coordinateSwap_apply d i j x.1

theorem sphereCoordinate_square_integral_eq (d : ℕ)
    (i j : Fin (d + 1)) :
    (∫ x, sphereCoordinate d i x ^ 2 ∂surfaceMeasure d) =
      ∫ x, sphereCoordinate d j x ^ 2 ∂surfaceMeasure d := by
  have h := (sphereIsometry_measurePreserving d (coordinateSwap d i j)).integral_comp'
    (fun x : SpherePoint d => sphereCoordinate d i x ^ 2)
  change (∫ x, sphereCoordinate d i
      (sphereIsometry d (coordinateSwap d i j) x) ^ 2 ∂surfaceMeasure d) =
    (∫ x, sphereCoordinate d i x ^ 2 ∂surfaceMeasure d) at h
  simpa only [sphereCoordinate_swap] using h.symm

theorem sphereCoordinate_square_integral_eq_zero (d : ℕ)
    (i j : Fin (d + 1)) :
    (∫ x, sphereCoordinate d i x ^ 2 ∂alignedMeasure d 0) =
      ∫ x, sphereCoordinate d j x ^ 2 ∂alignedMeasure d 0 := by
  rw [alignedMeasure_zero, integral_smul_measure,
    integral_smul_measure, sphereCoordinate_square_integral_eq d i j]

/-- On the actual unit sphere, the squared coordinates sum pointwise to one. -/
theorem sphereCoordinate_sq_sum_eq_one (d : ℕ) (x : SpherePoint d) :
    (∑ i : Fin (d + 1), sphereCoordinate d i x ^ 2) = 1 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => ℝ) x.1
  rw [hx] at h
  simp only [one_pow, Real.norm_eq_abs, sq_abs] at h
  simpa only [sphereCoordinate] using h.symm

/-- Every coordinate of the actual normalized zero-field sphere has second
moment `1/(d+1)`. This follows from orthogonal invariance and the pointwise
unit-norm identity, with no assumed coordinate-law density. -/
theorem sphereCoordinate_square_mean_zero (d : ℕ) (i : Fin (d + 1)) :
    (∫ x, sphereCoordinate d i x ^ 2 ∂alignedMeasure d 0) =
      1 / (d + 1 : ℝ) := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  have hsum : (∑ j : Fin (d + 1),
      ∫ x, sphereCoordinate d j x ^ 2 ∂alignedMeasure d 0) = 1 := by
    calc
      (∑ j : Fin (d + 1),
          ∫ x, sphereCoordinate d j x ^ 2 ∂alignedMeasure d 0) =
          ∫ x, (∑ j : Fin (d + 1), sphereCoordinate d j x ^ 2)
            ∂alignedMeasure d 0 := by
              symm
              exact integral_finset_sum _
                (fun j _ => sphereCoordinate_square_integrable d j)
      _ = ∫ _x : SpherePoint d, (1 : ℝ) ∂alignedMeasure d 0 := by
        congr 1
        funext x
        exact sphereCoordinate_sq_sum_eq_one d x
      _ = 1 := by simp
  let m : ℝ := ∫ x, sphereCoordinate d 0 x ^ 2 ∂alignedMeasure d 0
  have heqsum : (∑ j : Fin (d + 1),
      ∫ x, sphereCoordinate d j x ^ 2 ∂alignedMeasure d 0) =
        (d + 1 : ℝ) * m := by
    calc
      _ = ∑ _j : Fin (d + 1), m := by
        apply Finset.sum_congr rfl
        intro j _
        exact sphereCoordinate_square_integral_eq_zero d j 0
      _ = (d + 1 : ℝ) * m := by simp [m, nsmul_eq_mul]
  have hmul : (d + 1 : ℝ) * m = 1 := heqsum ▸ hsum
  have hd : (0 : ℝ) < (d + 1 : ℝ) := by positivity
  have hm : m = 1 / (d + 1 : ℝ) := by
    apply (eq_div_iff hd.ne').2
    nlinarith
  exact (sphereCoordinate_square_integral_eq_zero d i 0).trans hm

theorem fieldCoordinate_square_mean_zero (d : ℕ) :
    (∫ x, fieldCoordinate d x ^ 2 ∂alignedMeasure d 0) =
      1 / (d + 1 : ℝ) := by
  exact sphereCoordinate_square_mean_zero d 0

theorem fieldCoordinate_memLp_zero (d : ℕ) :
    MemLp (fieldCoordinate d) 2 (alignedMeasure d 0) := by
  apply (memLp_two_iff_integrable_sq
    (fieldCoordinate_continuous d).aestronglyMeasurable).2
  exact sphereCoordinate_square_integrable d 0

theorem sphereCoordinate_memLp_zero (d : ℕ) (i : Fin (d + 1)) :
    MemLp (sphereCoordinate d i) 2 (alignedMeasure d 0) := by
  apply (memLp_two_iff_integrable_sq
    (sphereCoordinate_continuous d i).aestronglyMeasurable).2
  exact sphereCoordinate_square_integrable d i

theorem sphereCoordinate_variance_zero (d : ℕ) (i : Fin (d + 1)) :
    sphereVariance d 0 (sphereCoordinate d i) = 1 / (d + 1 : ℝ) := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  have h := ProbabilityTheory.variance_eq_sub
    (sphereCoordinate_memLp_zero d i)
  simpa [sphereVariance, sphereCoordinate_mean_zero d i,
    sphereCoordinate_square_mean_zero d i] using h

/-- The exact denominator of the original zero-field Rayleigh quotient for
the field-axis coordinate, in ambient dimension `d+1`. -/
theorem fieldCoordinate_variance_zero (d : ℕ) :
    sphereVariance d 0 (fieldCoordinate d) = 1 / (d + 1 : ℝ) := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  have h := ProbabilityTheory.variance_eq_sub (fieldCoordinate_memLp_zero d)
  simpa [sphereVariance, fieldCoordinate_aligned_zero_mean d,
    fieldCoordinate_square_mean_zero d] using h

end

end DFL.Spectral
