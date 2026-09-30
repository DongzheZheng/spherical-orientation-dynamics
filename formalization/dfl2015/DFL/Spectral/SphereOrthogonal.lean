import DFL.Spectral.SphereSymmetry

/-!
# Orthogonal invariance of the original surface measure
-/

namespace DFL.Spectral

open MeasureTheory Metric
open scoped Pointwise ENNReal

noncomputable section

def sphereIsometry (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (x : SpherePoint d) : SpherePoint d :=
  ⟨U x.1, by
    have hx : ‖(x.1 : Ambient d)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.2
    simpa only [Metric.mem_sphere, dist_zero_right, U.norm_map] using hx⟩

theorem sphereIsometry_symm_apply (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (x : SpherePoint d) :
    sphereIsometry d U.symm (sphereIsometry d U x) = x := by
  ext
  simp [sphereIsometry]

theorem sphereIsometry_continuous (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Continuous (sphereIsometry d U) := by
  unfold sphereIsometry
  fun_prop

private theorem sphereIsometry_cone (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (s : Set (SpherePoint d)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereIsometry d U ⁻¹' s)) =
      U.symm '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨a • (sphereIsometry d U ω : Ambient d), ?_, ?_⟩
    · exact ⟨a, ha, (sphereIsometry d U ω : Ambient d),
        ⟨sphereIsometry d U ω, hω, rfl⟩, rfl⟩
    · simp [sphereIsometry, map_smul]
  · rintro ⟨z, ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, (sphereIsometry d U.symm ω : Ambient d), ?_, ?_⟩
    · refine ⟨sphereIsometry d U.symm ω, ?_, rfl⟩
      have hback : sphereIsometry d U (sphereIsometry d U.symm ω) = ω := by
        simpa using sphereIsometry_symm_apply d U.symm ω
      simpa [hback] using hω
    · simp [sphereIsometry, map_smul]

theorem surfaceMeasure_isometry_preimage (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (s : Set (SpherePoint d)) (hs : MeasurableSet s) :
    surfaceMeasure d (sphereIsometry d U ⁻¹' s) = surfaceMeasure d s := by
  have hpre : MeasurableSet (sphereIsometry d U ⁻¹' s) :=
    hs.preimage (sphereIsometry_continuous d U).measurable
  change (volume : Measure (Ambient d)).toSphere (sphereIsometry d U ⁻¹' s) =
    (volume : Measure (Ambient d)).toSphere s
  rw [Measure.toSphere_apply' (volume : Measure (Ambient d)) hpre,
    Measure.toSphere_apply' (volume : Measure (Ambient d)) hs,
    sphereIsometry_cone]
  congr 1
  let T := U.symm
  have hpres : MeasurePreserving T := T.measurePreserving
  calc
    volume (T '' (Set.Ioo (0 : ℝ) 1 •
      ((Subtype.val : SpherePoint d → Ambient d) '' s))) =
        ((volume : Measure (Ambient d)).map T)
          (T '' (Set.Ioo (0 : ℝ) 1 •
            ((Subtype.val : SpherePoint d → Ambient d) '' s))) := by
              rw [hpres.map_eq]
    _ = volume (T ⁻¹' (T '' (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : SpherePoint d → Ambient d) '' s)))) := by
            exact (T.toHomeomorph.measurableEmbedding).map_apply _ _
    _ = volume (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : SpherePoint d → Ambient d) '' s)) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have h : y = x := T.injective hxy
        simpa [h] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩

def sphereIsometryMeasurableEquiv (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) : SpherePoint d ≃ᵐ SpherePoint d where
  toFun := sphereIsometry d U
  invFun := sphereIsometry d U.symm
  left_inv := sphereIsometry_symm_apply d U
  right_inv := by
    intro x
    simpa using sphereIsometry_symm_apply d U.symm x
  measurable_toFun := (sphereIsometry_continuous d U).measurable
  measurable_invFun := (sphereIsometry_continuous d U.symm).measurable

theorem sphereIsometry_measurePreserving (d : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    MeasurePreserving (sphereIsometryMeasurableEquiv d U)
      (surfaceMeasure d) (surfaceMeasure d) := by
  refine ⟨(sphereIsometry_continuous d U).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometryMeasurableEquiv d U).measurable hs]
  exact surfaceMeasure_isometry_preimage d U s hs

end

end DFL.Spectral
