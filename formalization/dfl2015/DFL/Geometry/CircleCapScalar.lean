import DFL.Geometry.SuccCapSliceFormula

/-!
# Concrete scalar Fubini kernel for the original unit circle

This specializes the genuine `toSphere` cap reduction to ambient dimension
two. The one-dimensional transverse-ball volume is made explicit. The
remaining square-root integral is not evaluated here.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

theorem volume_ball_ambient_one (r : ℝ) :
    volume (Metric.ball (0 : Ambient 1) r) =
      ENNReal.ofReal r * 2 := by
  have hdim : Module.finrank ℝ (Ambient 1) = 2 * 0 + 1 := by simp
  simpa using
    InnerProductSpace.volume_ball_of_dim_odd (k := 0) hdim
      (0 : Ambient 1) r

def circleSliceReal (t s : ℝ) : ℝ :=
  if 0 < s ∧ s < t then
    2 * (s * Real.sqrt (1 - t ^ 2) / t)
  else if t ≤ s ∧ s < 1 then
    2 * Real.sqrt (1 - s ^ 2)
  else 0

theorem capSliceVolume_one (t s : ℝ) :
    capSliceVolume 1 t s = ENNReal.ofReal (circleSliceReal t s) := by
  unfold capSliceVolume circleSliceReal
  split_ifs with hsmall hlarge
  · rw [volume_ball_ambient_one]
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    simp
    ac_rfl
  · rw [volume_ball_ambient_one]
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    simp
    ac_rfl
  · simp

/-- The actual circle first-coordinate strict upper tail is exactly the
Lebesgue integral of an elementary square-root kernel. -/
theorem coordinateLaw_two_Ioi_circle_kernel (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    coordinateLaw 2 two_pos (Set.Ioi t) =
      (2 : ℝ≥0∞) * ∫⁻ s : ℝ, ENNReal.ofReal (circleSliceReal t s) := by
  have h := coordinateLaw_succ_Ioi_gamma 1 (by decide) t ht ht1
  have hkernel : (fun s : ℝ => scalarCapKernel 1 t s) =
      (fun s : ℝ => ENNReal.ofReal (circleSliceReal t s)) := by
    funext s
    rw [← capSliceVolume_eq_scalarCapKernel 1 (by decide) t s,
      capSliceVolume_one t s]
  rw [hkernel] at h
  norm_num at h
  exact h

end

end DFL.Geometry
