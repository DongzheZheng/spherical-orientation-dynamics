import DFL.Geometry.SuccSplit

/-!
# Genuine spherical-cap cones in every successor dimension

This reduces the original `volume.toSphere` cap measure to a Fubini integral
over Euclidean `(n-1)`-dimensional sections. No beta density or spherical
coordinate Jacobian is assumed.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

private theorem succ_pos (m : ℕ) : 0 < m + 1 := by omega

def sphereCapSucc (m : ℕ) (t : ℝ) : Set (UnitSphere (m + 1)) :=
  {ω | t < coordinate (m + 1) (succ_pos m) ω}

def coneCapSucc (m : ℕ) (t : ℝ) : Set (Ambient (m + 1)) :=
  Set.Ioo (0 : ℝ) 1 • ((↑) '' sphereCapSucc m t)

theorem sphereCapSucc_measurable (m : ℕ) (t : ℝ) :
    MeasurableSet (sphereCapSucc m t) := by
  change MeasurableSet ((coordinate (m + 1) (succ_pos m)) ⁻¹' Set.Ioi t)
  exact isOpen_Ioi.measurableSet.preimage
    (continuous_coordinate (m + 1) (succ_pos m)).measurable

theorem area_sphereCapSucc (m : ℕ) (t : ℝ) :
    area (m + 1) (sphereCapSucc m t) =
      (m + 1 : ℝ≥0∞) * volume (coneCapSucc m t) := by
  change (volume : Measure (Ambient (m + 1))).toSphere (sphereCapSucc m t) =
    (m + 1 : ℝ≥0∞) * volume (coneCapSucc m t)
  simpa [coneCapSucc] using
    Measure.toSphere_apply' (volume : Measure (Ambient (m + 1)))
      (sphereCapSucc_measurable m t)

theorem mem_coneCapSucc_iff (m : ℕ) (t : ℝ) (x : Ambient (m + 1)) :
    x ∈ coneCapSucc m t ↔
      0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ < x ⟨0, by omega⟩ := by
  constructor
  · intro hx
    rcases hx with ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    have hnormω : ‖(ω : Ambient (m + 1))‖ = (1 : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
    have hnorm : ‖a • (ω : Ambient (m + 1))‖ = a := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos ha.1, hnormω]
    have hc : (a • (ω : Ambient (m + 1))) ⟨0, by omega⟩ =
        a * coordinate (m + 1) (succ_pos m) ω := by
      simp [coordinate]
    change t < coordinate (m + 1) (succ_pos m) ω at hω
    refine ⟨by simpa [hnorm] using ha.1, by simpa [hnorm] using ha.2, ?_⟩
    rw [hnorm, hc]
    calc
      t * a = a * t := mul_comm _ _
      _ < a * coordinate (m + 1) (succ_pos m) ω :=
        mul_lt_mul_of_pos_left hω ha.1
  · rintro ⟨hx0, hx1, hxt⟩
    let a : ℝ := ‖x‖
    have ha : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    have hane : a ≠ 0 := ne_of_gt hx0
    let ω : UnitSphere (m + 1) := ⟨a⁻¹ • x, by
      have hnorm : ‖a⁻¹ • x‖ = (1 : ℝ) := by
        simp [norm_smul, a, hane]
      simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
    have hω : ω ∈ sphereCapSucc m t := by
      change t < coordinate (m + 1) (succ_pos m) ω
      have hdiv : t < x ⟨0, by omega⟩ / a := (lt_div_iff₀ hx0).2 hxt
      simpa [coordinate, ω, div_eq_mul_inv, mul_comm] using hdiv
    change x ∈ Set.Ioo (0 : ℝ) 1 • ((↑) '' sphereCapSucc m t)
    refine ⟨a, ha, (ω : Ambient (m + 1)), ⟨ω, hω, rfl⟩, ?_⟩
    change a • (a⁻¹ • x) = x
    simp [smul_smul, hane]

theorem coneCapSucc_isOpen (m : ℕ) (t : ℝ) :
    IsOpen (coneCapSucc m t) := by
  have heq : coneCapSucc m t =
      {x : Ambient (m + 1) | (0 : ℝ) < ‖x‖} ∩
      {x : Ambient (m + 1) | ‖x‖ < (1 : ℝ)} ∩
      {x : Ambient (m + 1) | t * ‖x‖ < x ⟨0, by omega⟩} := by
    ext x
    simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc] using
      mem_coneCapSucc_iff m t x
  rw [heq]
  exact ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).inter
    (isOpen_lt (continuous_const.mul continuous_norm) (by fun_prop))

/-- Exact dimension-independent Fubini reduction for the original
cone-induced spherical cap. This keeps the true geometric source throughout. -/
theorem coneCapSucc_volume_fubini (m : ℕ) (t : ℝ) :
    volume (coneCapSucc m t) =
      ∫⁻ s : ℝ, volume {y : Ambient m |
        (splitSucc m).symm (s, y) ∈ coneCapSucc m t} := by
  have hs : MeasurableSet (coneCapSucc m t) :=
    (coneCapSucc_isOpen m t).measurableSet
  have hmp : MeasurePreserving (splitSucc m).symm :=
    (splitSucc_measurePreserving m).symm (splitSucc m)
  have hs' : MeasurableSet ((splitSucc m).symm ⁻¹' coneCapSucc m t) :=
    hs.preimage (splitSucc m).symm.measurable
  calc
    volume (coneCapSucc m t) =
        (volume : Measure (ℝ × Ambient m)).map (splitSucc m).symm
          (coneCapSucc m t) := by rw [hmp.map_eq]
    _ = (volume : Measure (ℝ × Ambient m))
        ((splitSucc m).symm ⁻¹' coneCapSucc m t) :=
          Measure.map_apply (splitSucc m).symm.measurable hs
    _ = ∫⁻ s : ℝ, volume {y : Ambient m |
        (splitSucc m).symm (s, y) ∈ coneCapSucc m t} := by
          rw [Measure.volume_eq_prod, Measure.prod_apply hs']
          rfl

end

end DFL.Geometry
