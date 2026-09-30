import DFL.Geometry.SuccSplit

/-!
# The original spherical equator has zero area in every successor dimension

This statement concerns the first-coordinate pushforward of the actual
`volume.toSphere` measure. It does not use a proposed beta-density formula.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

private theorem succ_pos (m : ℕ) : 0 < m + 1 := by omega

/-- The first-coordinate hyperplane has zero ambient Euclidean volume. -/
theorem succ_coordinate_hyperplane_volume_zero (m : ℕ) :
    (volume : Measure (Ambient (m + 1)))
      {x | x ⟨0, succ_pos m⟩ = (0 : ℝ)} = 0 := by
  let H : Set (Ambient (m + 1)) :=
    {x | x ⟨0, succ_pos m⟩ = (0 : ℝ)}
  have hH : MeasurableSet H := by
    change MeasurableSet ((fun x : Ambient (m + 1) => x ⟨0, succ_pos m⟩) ⁻¹' {0})
    exact (by fun_prop : Measurable fun x : Ambient (m + 1) =>
      x ⟨0, succ_pos m⟩) (measurableSet_singleton (0 : ℝ))
  have hmp : MeasurePreserving (splitSucc m).symm :=
    (splitSucc_measurePreserving m).symm (splitSucc m)
  have heq : (splitSucc m).symm ⁻¹' H =
      ({0} : Set ℝ) ×ˢ Set.univ := by
    ext ⟨s, y⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true, H]
    rw [splitSucc_symm_fst]
  have hprod : (volume : Measure (ℝ × Ambient m))
      (({0} : Set ℝ) ×ˢ Set.univ) = 0 := by
    apply le_antisymm
    · calc
        (volume : Measure (ℝ × Ambient m))
            (({0} : Set ℝ) ×ˢ Set.univ) =
            ((volume : Measure ℝ).prod (volume : Measure (Ambient m)))
              (({0} : Set ℝ) ×ˢ Set.univ) := by rw [Measure.volume_eq_prod]
        _ ≤ (volume : Measure ℝ) {0} *
            (volume : Measure (Ambient m)) Set.univ := Measure.prod_prod_le _ _
        _ = 0 := by simp
    · exact zero_le _
  change (volume : Measure (Ambient (m + 1))) H = 0
  calc
    (volume : Measure (Ambient (m + 1))) H =
        (volume : Measure (ℝ × Ambient m)).map (splitSucc m).symm H := by
          rw [hmp.map_eq]
    _ = (volume : Measure (ℝ × Ambient m)) ((splitSucc m).symm ⁻¹' H) :=
      Measure.map_apply (splitSucc m).symm.measurable hH
    _ = 0 := by rw [heq, hprod]

/-- The equator of the actual unit sphere carries zero `volume.toSphere` area. -/
theorem area_succ_equator_zero (m : ℕ) :
    area (m + 1) {ω | coordinate (m + 1) (succ_pos m) ω = 0} = 0 := by
  let E : Set (UnitSphere (m + 1)) :=
    {ω | coordinate (m + 1) (succ_pos m) ω = 0}
  let C : Set (Ambient (m + 1)) := Set.Ioo (0 : ℝ) 1 • ((↑) '' E)
  let H : Set (Ambient (m + 1)) :=
    {x | x ⟨0, succ_pos m⟩ = (0 : ℝ)}
  have hE : MeasurableSet E := by
    change MeasurableSet ((coordinate (m + 1) (succ_pos m)) ⁻¹' {0})
    exact (measurableSet_singleton (0 : ℝ)).preimage
      (continuous_coordinate (m + 1) (succ_pos m)).measurable
  have hCH : C ⊆ H := by
    intro x hx
    rcases hx with ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    change (a • (ω : Ambient (m + 1))) ⟨0, succ_pos m⟩ = 0
    change coordinate (m + 1) (succ_pos m) ω = 0 at hω
    simp [coordinate] at hω ⊢
    simp [hω]
  have hC : (volume : Measure (Ambient (m + 1))) C = 0 :=
    measure_mono_null hCH (succ_coordinate_hyperplane_volume_zero m)
  change area (m + 1) E = 0
  change (volume : Measure (Ambient (m + 1))).toSphere E = 0
  rw [Measure.toSphere_apply' (volume : Measure (Ambient (m + 1))) hE]
  rw [finrank_euclideanSpace_fin]
  change ((m + 1 : ℕ) : ℝ≥0∞) *
    (volume : Measure (Ambient (m + 1))) C = 0
  rw [hC, mul_zero]

/-- Every successor-dimensional original first-coordinate law is atomless
at the equator. This includes the physical circle and two-sphere. -/
theorem coordinateLaw_succ_singleton_zero (m : ℕ) :
    coordinateLaw (m + 1) (succ_pos m) ({0} : Set ℝ) = 0 := by
  rw [coordinateLaw, Measure.map_apply
    (continuous_coordinate (m + 1) (succ_pos m)).measurable
    (measurableSet_singleton (0 : ℝ))]
  exact area_succ_equator_zero m

end

end DFL.Geometry
