import DFL.Geometry.MomentBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# From the actual circle coordinate law to the DFL marginal

The premise is an equality of Borel measures on the original circle's
first-coordinate pushforward. Mathlib's Chebyshev measure is the exact
arcsine density, so its integration theorem supplies the endpoint-singular
`n=2` marginal without inserting an integrability assumption in the target.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Interval ENNReal

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

private theorem marginalWeight_two_eq
    (r t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    DFL.marginalWeight 2 r t =
      Real.exp (r * t) * (Real.sqrt (1 - t ^ 2))⁻¹ := by
  have hw : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold DFL.marginalWeight
  norm_num
  rw [show (-(1 / 2) : ℝ) = (-1) / 2 by ring,
    Real.rpow_div_two_eq_sqrt (-1) hw]
  rw [Real.rpow_neg_one]

/-- The original circle's arcsine coordinate law yields both DFL moments
with the same geometric factor `2`, independent of field strength. -/
theorem sphereMomentBridge_two_of_coordinateLaw
    (hLaw : coordinateLaw 2 two_pos =
      (2 : ENNReal) • Polynomial.Chebyshev.measureT) :
    SphereMomentBridge 2 two_pos := by
  refine ⟨2, by norm_num, ?_⟩
  intro r
  constructor
  · rw [spherePartition_eq_coordinateLaw_integral, hLaw, integral_smul_measure]
    simp only [ENNReal.toReal_ofNat, smul_eq_mul]
    congr 1
    rw [Polynomial.Chebyshev.integral_measureT]
    unfold DFL.partition
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    dsimp only
    rw [Real.sqrt_inv]
    simp only [marginalWeight_two_eq r t ht']
  · rw [sphereFirstMoment_eq_coordinateLaw_integral, hLaw, integral_smul_measure]
    simp only [ENNReal.toReal_ofNat, smul_eq_mul]
    congr 1
    rw [Polynomial.Chebyshev.integral_measureT]
    unfold DFL.firstMoment
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    dsimp only
    rw [Real.sqrt_inv]
    simp only [marginalWeight_two_eq r t ht']
    ring

/-- Consequently the physical circle case of the 2015 single-valley
conjecture follows from the exact original circle coordinate law. -/
theorem sphere_isUnimodal_two_of_coordinateLaw
    (hLaw : coordinateLaw 2 two_pos =
      (2 : ENNReal) • Polynomial.Chebyshev.measureT) :
    SphereIsUnimodal 2 two_pos :=
  sphere_isUnimodal_of_moment_bridge 2 (by decide)
    (sphereMomentBridge_two_of_coordinateLaw hLaw)

end

end DFL.Geometry
