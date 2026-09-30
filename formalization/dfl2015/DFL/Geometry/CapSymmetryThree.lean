import DFL.Geometry.CapToLaw

/-!
# Antipodal symmetry of the true three-dimensional cone-induced sphere

This is proved from Euclidean volume invariance under negation and the
defining cone formula, rather than postulating symmetry of a beta law.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

private theorem three_pos : 0 < (3 : ℕ) := by decide

def antipodalThree (ω : UnitSphere 3) : UnitSphere 3 :=
  ⟨-ω.1, by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using ω.2⟩

theorem antipodalThree_involutive (ω : UnitSphere 3) :
    antipodalThree (antipodalThree ω) = ω := by
  ext
  simp [antipodalThree]

theorem antipodalThree_coordinate (ω : UnitSphere 3) :
    coordinate 3 three_pos (antipodalThree ω) =
      -coordinate 3 three_pos ω := by
  simp [coordinate, antipodalThree]

def lowerCapThree (t : ℝ) : Set (UnitSphere 3) :=
  {ω | coordinate 3 three_pos ω < -t}

theorem lowerCapThree_eq_preimage (t : ℝ) :
    lowerCapThree t = antipodalThree ⁻¹' sphereCapThree t := by
  ext ω
  simp only [lowerCapThree, sphereCapThree, Set.mem_setOf_eq, Set.mem_preimage,
    antipodalThree_coordinate]
  constructor <;> intro h <;> linarith

theorem antipodal_cone (s : Set (UnitSphere 3)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' (antipodalThree ⁻¹' s)) =
      (fun x : Ambient 3 => -x) '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨a • (antipodalThree ω : Ambient 3), ?_, ?_⟩
    · exact ⟨a, ha, (antipodalThree ω : Ambient 3),
        ⟨antipodalThree ω, hω, rfl⟩, rfl⟩
    · simp [antipodalThree, smul_neg]
  · rintro ⟨z, ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, (antipodalThree ω : Ambient 3), ?_, ?_⟩
    · refine ⟨antipodalThree ω, ?_, rfl⟩
      simpa [antipodalThree_involutive] using hω
    · simp [antipodalThree, smul_neg]

theorem volume_neg_image_coneCapThree (t : ℝ) :
    volume ((fun x : Ambient 3 => -x) '' coneCapThree t) =
      volume (coneCapThree t) := by
  have hmeas : MeasurableSet ((fun x : Ambient 3 => -x) '' coneCapThree t) := by
    exact measurableEmbedding_neg.measurableSet_image.mpr
      (coneCapThree_isOpen t).measurableSet
  calc
    volume ((fun x : Ambient 3 => -x) '' coneCapThree t) =
        ((volume : Measure (Ambient 3)).map (fun x => -x))
          ((fun x : Ambient 3 => -x) '' coneCapThree t) := by
            rw [Measure.map_neg_eq_self]
    _ = volume ((fun x : Ambient 3 => -x) ⁻¹'
        ((fun x : Ambient 3 => -x) '' coneCapThree t)) :=
          Measure.map_apply measurable_neg hmeas
    _ = volume (coneCapThree t) := by
          congr 1
          ext x
          simp

theorem area_lowerCapThree_eq_upper (t : ℝ) :
    area 3 (lowerCapThree t) = area 3 (sphereCapThree t) := by
  have hmeas : MeasurableSet (lowerCapThree t) := by
    change MeasurableSet ((coordinate 3 three_pos) ⁻¹' Set.Iio (-t))
    exact measurableSet_Iio.preimage (continuous_coordinate 3 three_pos).measurable
  change (volume : Measure (Ambient 3)).toSphere (lowerCapThree t) =
    (volume : Measure (Ambient 3)).toSphere (sphereCapThree t)
  rw [Measure.toSphere_apply' (volume : Measure (Ambient 3)) hmeas,
    Measure.toSphere_apply' (volume : Measure (Ambient 3))
      (sphereCapThree_measurable t)]
  rw [lowerCapThree_eq_preimage, antipodal_cone, ← coneCapThree]
  simp

end

end DFL.Geometry
