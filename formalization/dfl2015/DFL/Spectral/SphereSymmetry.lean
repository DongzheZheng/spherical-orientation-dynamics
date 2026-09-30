import DFL.Spectral.SphereMeasure

/-!
# Antipodal symmetry on the original sphere

The proofs use the cone definition of the original spherical surface measure
and invariance of ambient Euclidean volume. No coordinate law is postulated.
-/

namespace DFL.Spectral

open MeasureTheory Metric
open scoped Pointwise ENNReal

noncomputable section

def antipodal (d : ℕ) (x : SpherePoint d) : SpherePoint d :=
  ⟨-x.1, by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using x.2⟩

theorem antipodal_involutive (d : ℕ) (x : SpherePoint d) :
    antipodal d (antipodal d x) = x := by
  ext
  simp [antipodal]

theorem antipodal_coordinate (d : ℕ) (x : SpherePoint d) :
    fieldCoordinate d (antipodal d x) = -fieldCoordinate d x := by
  simp [fieldCoordinate, antipodal]

theorem antipodal_continuous (d : ℕ) : Continuous (antipodal d) := by
  unfold antipodal
  fun_prop

private theorem antipodal_cone (d : ℕ) (s : Set (SpherePoint d)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' (antipodal d ⁻¹' s)) =
      (fun x : Ambient d => -x) '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨a • (antipodal d ω : Ambient d), ?_, ?_⟩
    · exact ⟨a, ha, (antipodal d ω : Ambient d),
        ⟨antipodal d ω, hω, rfl⟩, rfl⟩
    · simp [antipodal, smul_neg]
  · rintro ⟨z, ⟨a, ha, y, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, (antipodal d ω : Ambient d), ?_, ?_⟩
    · refine ⟨antipodal d ω, ?_, rfl⟩
      simpa [antipodal_involutive] using hω
    · simp [antipodal, smul_neg]

/-- Antipodal symmetry of the actual cone-induced spherical measure in every
dimension, proved from ambient volume invariance. -/
theorem surfaceMeasure_antipodal_preimage (d : ℕ)
    (s : Set (SpherePoint d)) (hs : MeasurableSet s) :
    surfaceMeasure d (antipodal d ⁻¹' s) = surfaceMeasure d s := by
  have hpre : MeasurableSet (antipodal d ⁻¹' s) :=
    hs.preimage (antipodal_continuous d).measurable
  change (volume : Measure (Ambient d)).toSphere (antipodal d ⁻¹' s) =
    (volume : Measure (Ambient d)).toSphere s
  rw [Measure.toSphere_apply' (volume : Measure (Ambient d)) hpre,
    Measure.toSphere_apply' (volume : Measure (Ambient d)) hs,
    antipodal_cone]
  congr 1
  calc
    volume ((fun x : Ambient d => -x) ''
      (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : SpherePoint d → Ambient d) '' s))) =
        ((volume : Measure (Ambient d)).map fun x => -x)
          ((fun x : Ambient d => -x) ''
            (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : SpherePoint d → Ambient d) '' s))) := by
              rw [Measure.map_neg_eq_self]
    _ = volume ((fun x : Ambient d => -x) ⁻¹'
        ((fun x : Ambient d => -x) ''
          (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : SpherePoint d → Ambient d) '' s)))) :=
      MeasurableEmbedding.map_apply measurableEmbedding_neg _ _
    _ = volume (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : SpherePoint d → Ambient d) '' s)) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have h : y = x := neg_injective hxy
        simpa [h] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩

def antipodalMeasurableEquiv (d : ℕ) : SpherePoint d ≃ᵐ SpherePoint d where
  toFun := antipodal d
  invFun := antipodal d
  left_inv := antipodal_involutive d
  right_inv := antipodal_involutive d
  measurable_toFun := (antipodal_continuous d).measurable
  measurable_invFun := (antipodal_continuous d).measurable

theorem antipodal_measurePreserving (d : ℕ) :
    MeasurePreserving (antipodalMeasurableEquiv d)
      (surfaceMeasure d) (surfaceMeasure d) := by
  refine ⟨(antipodal_continuous d).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (antipodalMeasurableEquiv d).measurable hs]
  exact surfaceMeasure_antipodal_preimage d s hs

/-- The original unweighted sphere has zero mean in the field direction. -/
theorem fieldCoordinate_surface_mean_zero (d : ℕ) :
    ∫ x, fieldCoordinate d x ∂surfaceMeasure d = 0 := by
  have h := (antipodal_measurePreserving d).integral_comp' (fieldCoordinate d)
  have hneg : (∫ x, -fieldCoordinate d x ∂surfaceMeasure d) =
      ∫ x, fieldCoordinate d x ∂surfaceMeasure d := by
    simpa [antipodalMeasurableEquiv, antipodal_coordinate] using h
  rw [integral_neg] at hneg
  linarith

/-- The normalized zero-field law has zero field-coordinate mean. -/
theorem fieldCoordinate_aligned_zero_mean (d : ℕ) :
    ∫ x, fieldCoordinate d x ∂alignedMeasure d 0 = 0 := by
  rw [alignedMeasure_zero, integral_smul_measure,
    fieldCoordinate_surface_mean_zero]
  simp

end

end DFL.Spectral
