import DFL.Geometry.SphereMeasure

/-!
# Scalar calculation in the three-dimensional cone-cap route

For a spherical cap with threshold t in (0,1), slicing the corresponding
unit-ball cone perpendicular to the first coordinate gives two disk-radius
regimes. This file verifies their exact elementary integral, independently
of the still-unproved Euclidean-volume Fubini reduction of that cone.
-/

namespace DFL.Geometry

open MeasureTheory intervalIntegral

noncomputable section

/-- The sum of the two cross-sectional disk areas equals the cone volume
predicted by the uniform first-coordinate law on S². This is the scalar
calculus part only; it is not yet a theorem about Measure.toSphere. -/
theorem threeDimensionalConeCap_slice_integral
    (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, Real.pi * (s ^ 2 * ((1 - t ^ 2) / t ^ 2))) +
      (∫ s in t..1, Real.pi * (1 - s ^ 2)) =
        (2 * Real.pi / 3) * (1 - t) := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hfirst :
      (∫ s in (0 : ℝ)..t, Real.pi * (s ^ 2 * ((1 - t ^ 2) / t ^ 2))) =
        Real.pi * ((1 - t ^ 2) / t ^ 2) * (t ^ 3 / 3) := by
    have hp : (fun s : ℝ => Real.pi * (s ^ 2 * ((1 - t ^ 2) / t ^ 2))) =
        fun s => (Real.pi * ((1 - t ^ 2) / t ^ 2)) * s ^ 2 := by
      funext s
      ring
    rw [hp, intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hsecond :
      (∫ s in t..1, Real.pi * (1 - s ^ 2)) =
        Real.pi * ((1 - t) - (1 - t ^ 3) / 3) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
        (intervalIntegrable_pow 2),
      intervalIntegral.integral_const, integral_pow]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hfirst, hsecond]
  field_simp
  ring

end

end DFL.Geometry
