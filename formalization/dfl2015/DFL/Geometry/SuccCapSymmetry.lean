import DFL.Geometry.SuccCapFubini

/-!
# Antipodal invariance of the actual cap measure in all dimensions

The result is derived from Euclidean volume invariance under negation and
`Measure.toSphere_apply'`, not from a presumed symmetric beta density.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

private theorem succ_pos (m : ℕ) : 0 < m + 1 := by omega

def antipodalSucc (m : ℕ) (ω : UnitSphere (m + 1)) :
    UnitSphere (m + 1) :=
  ⟨-ω.1, by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using ω.2⟩

theorem antipodalSucc_involutive (m : ℕ) (ω : UnitSphere (m + 1)) :
    antipodalSucc m (antipodalSucc m ω) = ω := by
  ext
  simp [antipodalSucc]

theorem antipodalSucc_coordinate (m : ℕ) (ω : UnitSphere (m + 1)) :
    coordinate (m + 1) (succ_pos m) (antipodalSucc m ω) =
      -coordinate (m + 1) (succ_pos m) ω := by
  simp [coordinate, antipodalSucc]

def lowerCapSucc (m : ℕ) (t : ℝ) : Set (UnitSphere (m + 1)) :=
  {ω | coordinate (m + 1) (succ_pos m) ω < -t}

theorem lowerCapSucc_eq_preimage (m : ℕ) (t : ℝ) :
    lowerCapSucc m t = antipodalSucc m ⁻¹' sphereCapSucc m t := by
  ext ω
  simp only [lowerCapSucc, sphereCapSucc, Set.mem_setOf_eq, Set.mem_preimage,
    antipodalSucc_coordinate]
  constructor <;> intro h <;> linarith

theorem antipodal_cone_succ (m : ℕ) (s : Set (UnitSphere (m + 1))) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' (antipodalSucc m ⁻¹' s)) =
      (fun x : Ambient (m + 1) => -x) ''
        (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨a • (antipodalSucc m ω : Ambient (m + 1)), ?_, ?_⟩
    · exact ⟨a, ha, (antipodalSucc m ω : Ambient (m + 1)),
        ⟨antipodalSucc m ω, hω, rfl⟩, rfl⟩
    · simp [antipodalSucc, smul_neg]
  · rintro ⟨z, ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, (antipodalSucc m ω : Ambient (m + 1)), ?_, ?_⟩
    · refine ⟨antipodalSucc m ω, ?_, rfl⟩
      simpa [antipodalSucc_involutive] using hω
    · simp [antipodalSucc, smul_neg]

theorem volume_neg_image_coneCapSucc (m : ℕ) (t : ℝ) :
    volume ((fun x : Ambient (m + 1) => -x) '' coneCapSucc m t) =
      volume (coneCapSucc m t) := by
  have hmeas : MeasurableSet
      ((fun x : Ambient (m + 1) => -x) '' coneCapSucc m t) := by
    exact measurableEmbedding_neg.measurableSet_image.mpr
      (coneCapSucc_isOpen m t).measurableSet
  calc
    volume ((fun x : Ambient (m + 1) => -x) '' coneCapSucc m t) =
        ((volume : Measure (Ambient (m + 1))).map (fun x => -x))
          ((fun x : Ambient (m + 1) => -x) '' coneCapSucc m t) := by
            rw [Measure.map_neg_eq_self]
    _ = volume ((fun x : Ambient (m + 1) => -x) ⁻¹'
        ((fun x : Ambient (m + 1) => -x) '' coneCapSucc m t)) :=
          Measure.map_apply measurable_neg hmeas
    _ = volume (coneCapSucc m t) := by
          congr 1
          ext x
          simp

theorem area_lowerCapSucc_eq_upper (m : ℕ) (t : ℝ) :
    area (m + 1) (lowerCapSucc m t) =
      area (m + 1) (sphereCapSucc m t) := by
  have hmeas : MeasurableSet (lowerCapSucc m t) := by
    change MeasurableSet ((coordinate (m + 1) (succ_pos m)) ⁻¹' Set.Iio (-t))
    exact measurableSet_Iio.preimage
      (continuous_coordinate (m + 1) (succ_pos m)).measurable
  change (volume : Measure (Ambient (m + 1))).toSphere (lowerCapSucc m t) =
    (volume : Measure (Ambient (m + 1))).toSphere (sphereCapSucc m t)
  rw [Measure.toSphere_apply' (volume : Measure (Ambient (m + 1))) hmeas,
    Measure.toSphere_apply' (volume : Measure (Ambient (m + 1)))
      (sphereCapSucc_measurable m t)]
  rw [lowerCapSucc_eq_preimage, antipodal_cone_succ, ← coneCapSucc]
  simp

end

end DFL.Geometry
