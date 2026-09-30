import DFL.Geometry.SuccBetaMeasure
import DFL.Geometry.MomentBridge

/-!
# Higher-dimensional beta-law to original spherical moment bridge

This module checks the final integration step for ambient dimensions
`n=k+3≥3`.  The Borel coordinate-law equality remains an explicit
hypothesis and is supplied by the separate geometric cap construction.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

private theorem betaPower_nonneg_local (k : ℕ) (t : ℝ) :
    0 ≤ betaPower k t := by
  unfold betaPower
  positivity

/-- Integrating against the independently defined beta measure is exactly
integrating against its density on the original coordinate interval. -/
theorem betaCoordinateMeasure_integral (k : ℕ) (f : ℝ → ℝ) :
    (∫ t : ℝ, f t ∂betaCoordinateMeasure k) =
      ∫ t in (-1 : ℝ)..1, f t * betaPower k t := by
  change (∫ t in Set.Icc (-1 : ℝ) 1, f t
      ∂(volume : Measure ℝ).withDensity
        (fun s : ℝ => ENNReal.ofReal (betaPower k s))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (by
      unfold betaPower
      fun_prop : Measurable (fun s : ℝ =>
        ENNReal.ofReal (betaPower k s)))
    (by simp : ∀ᵐ s ∂(volume : Measure ℝ).restrict
      (Set.Icc (-1 : ℝ) 1),
      ENNReal.ofReal (betaPower k s) < ∞)
    f measurableSet_Icc]
  have hpoint (t : ℝ) :
      (ENNReal.ofReal (betaPower k t)).toReal • f t =
        f t * betaPower k t := by
    rw [ENNReal.toReal_ofReal (betaPower_nonneg_local k t)]
    simp only [smul_eq_mul]
    ring
  simp_rw [hpoint]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

private theorem betaPower_marginal (k : ℕ) (r t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    DFL.marginalWeight (k + 3) r t =
      Real.exp (r * t) * betaPower k t := by
  have hw : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold DFL.marginalWeight betaPower
  have hexp : (((((k + 3 : ℕ) : ℝ) - 3) / 2)) =
      (k : ℝ) / 2 := by push_cast; ring
  rw [hexp]
  change Real.exp (r * t) * (1 - t ^ 2) ^ ((k : ℝ) / 2) =
    Real.exp (r * t) * Real.sqrt (1 - t ^ 2) ^ k
  rw [Real.rpow_div_two_eq_sqrt (k : ℝ) hw,
    Real.rpow_natCast]

/-- A full beta coordinate law with one positive field-independent factor
supplies both moments of the original physical sphere. -/
theorem sphereMomentBridge_succ_of_coordinateLaw (k : ℕ) (C : ℝ)
    (hC : 0 < C)
    (hLaw : coordinateLaw (k + 3) (by omega) =
      ENNReal.ofReal C • betaCoordinateMeasure k) :
    SphereMomentBridge (k + 3) (by omega) := by
  refine ⟨C, hC, ?_⟩
  intro r
  constructor
  · rw [spherePartition_eq_coordinateLaw_integral, hLaw,
      integral_smul_measure]
    rw [ENNReal.toReal_ofReal hC.le]
    simp only [smul_eq_mul]
    congr 1
    rw [betaCoordinateMeasure_integral]
    unfold DFL.partition
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact (betaPower_marginal k r t ht').symm
  · rw [sphereFirstMoment_eq_coordinateLaw_integral, hLaw,
      integral_smul_measure]
    rw [ENNReal.toReal_ofReal hC.le]
    simp only [smul_eq_mul]
    congr 1
    rw [betaCoordinateMeasure_integral]
    unfold DFL.firstMoment
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    dsimp only
    rw [betaPower_marginal k r t ht']
    ring

end

end DFL.Geometry
