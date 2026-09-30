import DFL.Geometry.ConeCapScalar

/-!
# The geometric cone behind a cap of the actual three-dimensional sphere

This exposes the exact Euclidean-volume set that must be evaluated to prove
the n = 3 first-coordinate pushforward. The missing step is a Fubini
calculation of its volume, not an identity between two defined measures.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

def sphereCapThree (t : ℝ) : Set (UnitSphere 3) :=
  {ω | t < coordinate 3 three_pos ω}

def coneCapThree (t : ℝ) : Set (Ambient 3) :=
  Set.Ioo (0 : ℝ) 1 • ((↑) '' sphereCapThree t)

theorem sphereCapThree_measurable (t : ℝ) : MeasurableSet (sphereCapThree t) := by
  change MeasurableSet ((coordinate 3 three_pos) ⁻¹' Set.Ioi t)
  exact isOpen_Ioi.measurableSet.preimage (continuous_coordinate 3 three_pos).measurable

theorem area_sphereCapThree (t : ℝ) :
    area 3 (sphereCapThree t) = (3 : ℝ≥0∞) * volume (coneCapThree t) := by
  change (volume : Measure (Ambient 3)).toSphere (sphereCapThree t) =
    (3 : ℝ≥0∞) * volume (coneCapThree t)
  simpa [coneCapThree] using
    Measure.toSphere_apply' (volume : Measure (Ambient 3))
      (sphereCapThree_measurable t)

/-- A cap cone is exactly a portion of the punctured unit ball cut by
the homogeneous inequality in the distinguished coordinate. -/
theorem mem_coneCapThree_iff (t : ℝ) (x : Ambient 3) :
    x ∈ coneCapThree t ↔
      0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ < x ⟨0, by decide⟩ := by
  constructor
  · intro hx
    rcases hx with ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    have hnormω : ‖(ω : Ambient 3)‖ = (1 : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
    have hnorm : ‖a • (ω : Ambient 3)‖ = a := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos ha.1, hnormω]
    have hc : (a • (ω : Ambient 3)) ⟨0, by decide⟩ =
        a * coordinate 3 three_pos ω := by
      simp [coordinate]
    change t < coordinate 3 three_pos ω at hω
    refine ⟨by simpa [hnorm] using ha.1, by simpa [hnorm] using ha.2, ?_⟩
    rw [hnorm, hc]
    calc
      t * a = a * t := mul_comm _ _
      _ < a * coordinate 3 three_pos ω := mul_lt_mul_of_pos_left hω ha.1
  · rintro ⟨hx0, hx1, hxt⟩
    let a : ℝ := ‖x‖
    have ha : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    have hane : a ≠ 0 := ne_of_gt hx0
    let ω : UnitSphere 3 := ⟨a⁻¹ • x, by
      have hnorm : ‖a⁻¹ • x‖ = (1 : ℝ) := by
        simp [norm_smul, a, hane]
      simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
    have hω : ω ∈ sphereCapThree t := by
      change t < coordinate 3 three_pos ω
      have hdiv : t < x ⟨0, by decide⟩ / a := (lt_div_iff₀ hx0).2 hxt
      simpa [coordinate, ω, div_eq_mul_inv, mul_comm] using hdiv
    change x ∈ Set.Ioo (0 : ℝ) 1 • ((↑) '' sphereCapThree t)
    refine ⟨a, ha, (ω : Ambient 3), ⟨ω, hω, rfl⟩, ?_⟩
    change a • (a⁻¹ • x) = x
    simp [smul_smul, hane]

end

end DFL.Geometry
