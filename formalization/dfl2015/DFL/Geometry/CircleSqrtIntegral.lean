import DFL.Geometry.CircleCapScalar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The circular-segment square-root integral

This is the elementary scalar identity required to evaluate the actual
two-dimensional spherical-cap cone. It does not assert a measure law.
-/

namespace DFL.Geometry

open MeasureTheory Set
open scoped Interval

noncomputable section

theorem integral_sqrt_one_sub_sq_to_one (t : ℝ)
    (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in t..1, Real.sqrt (1 - s ^ 2)) =
      (Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2 := by
  have hangle : -(Real.pi / 2) ≤ Real.arcsin t ∧
      Real.arcsin t ≤ Real.pi / 2 := Real.arcsin_mem_Icc t
  calc
    (∫ s in t..1, Real.sqrt (1 - s ^ 2)) =
        ∫ s in Real.sin (Real.arcsin t)..Real.sin (Real.pi / 2),
          Real.sqrt (1 - s ^ 2) := by
            rw [Real.sin_arcsin ht ht1, Real.sin_pi_div_two]
    _ = ∫ θ in Real.arcsin t..Real.pi / 2,
          Real.sqrt (1 - Real.sin θ ^ 2) * Real.cos θ :=
        (intervalIntegral.integral_comp_mul_deriv (fun θ _ => Real.hasDerivAt_sin θ)
          Real.continuous_cos.continuousOn (by fun_prop)).symm
    _ = ∫ θ in Real.arcsin t..Real.pi / 2, Real.cos θ ^ 2 := by
          apply intervalIntegral.integral_congr_ae (ae_of_all _ fun θ hθ => ?_)
          rw [uIoc_of_le hangle.2, Set.mem_Ioc] at hθ
          rw [← Real.cos_eq_sqrt_one_sub_sin_sq (hangle.1.trans hθ.1.le) hθ.2]
          ring
    _ = (Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2 := by
          rw [integral_cos_sq]
          rw [Real.cos_pi_div_two, Real.sin_pi_div_two,
            Real.cos_arcsin, Real.sin_arcsin ht ht1]
          unfold Real.arccos
          ring

end

end DFL.Geometry
