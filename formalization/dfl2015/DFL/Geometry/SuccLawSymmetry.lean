import DFL.Geometry.SuccCapSymmetry

/-!
# Reflection symmetry of the actual sphere-coordinate law

This uses the original cone-induced `volume.toSphere` area and Euclidean
volume preservation under negation. No marginal density is assumed.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem succ_pos (m : ℕ) : 0 < m + 1 := by omega

private theorem antipodalSucc_measurable (m : ℕ) :
    Measurable (antipodalSucc m) := by
  have hcont : Continuous (antipodalSucc m) := by
    unfold antipodalSucc
    fun_prop
  exact hcont.measurable

private theorem volume_neg_image_succ (m : ℕ) (s : Set (Ambient (m + 1))) :
    volume ((fun x : Ambient (m + 1) => -x) '' s) = volume s := by
  calc
    volume ((fun x : Ambient (m + 1) => -x) '' s) =
        ((volume : Measure (Ambient (m + 1))).map
          (fun x : Ambient (m + 1) => -x))
            ((fun x : Ambient (m + 1) => -x) '' s) := by
              rw [Measure.map_neg_eq_self]
    _ = volume ((fun x : Ambient (m + 1) => -x) ⁻¹'
        ((fun x : Ambient (m + 1) => -x) '' s)) :=
          measurableEmbedding_neg.map_apply volume _
    _ = volume s := by
      congr 1
      ext x
      simp

theorem area_antipodalSucc_preimage (m : ℕ)
    (s : Set (UnitSphere (m + 1))) (hs : MeasurableSet s) :
    area (m + 1) (antipodalSucc m ⁻¹' s) = area (m + 1) s := by
  have hpre : MeasurableSet (antipodalSucc m ⁻¹' s) :=
    hs.preimage (antipodalSucc_measurable m)
  change (volume : Measure (Ambient (m + 1))).toSphere
      (antipodalSucc m ⁻¹' s) =
    (volume : Measure (Ambient (m + 1))).toSphere s
  rw [Measure.toSphere_apply' (volume : Measure (Ambient (m + 1))) hpre,
    Measure.toSphere_apply' (volume : Measure (Ambient (m + 1))) hs,
    antipodal_cone_succ,
    volume_neg_image_succ]

theorem coordinateLaw_succ_map_neg (m : ℕ) :
    (coordinateLaw (m + 1) (succ_pos m)).map
        (fun x : ℝ => -x) = coordinateLaw (m + 1) (succ_pos m) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_neg hA,
    coordinateLaw, Measure.map_apply
      (continuous_coordinate (m + 1) (succ_pos m)).measurable
        (hA.preimage measurable_neg),
    Measure.map_apply
      (continuous_coordinate (m + 1) (succ_pos m)).measurable hA]
  let S : Set (UnitSphere (m + 1)) :=
    coordinate (m + 1) (succ_pos m) ⁻¹' A
  have hS : MeasurableSet S :=
    hA.preimage (continuous_coordinate (m + 1) (succ_pos m)).measurable
  have hpre : coordinate (m + 1) (succ_pos m) ⁻¹'
      ((fun x : ℝ => -x) ⁻¹' A) = antipodalSucc m ⁻¹' S := by
    ext ω
    simp only [Set.mem_preimage, S, antipodalSucc_coordinate]
  rw [hpre]
  exact area_antipodalSucc_preimage m S hS

end

end DFL.Geometry
