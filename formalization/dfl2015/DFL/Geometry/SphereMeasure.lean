import DFL.Targets

/-!
# The actual cone-induced measure on the Euclidean unit sphere

This module uses mathlib's Measure.toSphere applied to Euclidean volume.
It does not define a spherical measure by the desired beta-density formula.
The complete Borel pushforward is proved in `CircleLawFull.lean` for the
physical circle and `SuccLawFull.lean` for every higher dimension. Their
all-dimensional use is in `PhysicalSphereAll.lean`.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

/-- The cone-induced spherical area measure from Euclidean volume. -/
def area (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (Ambient n)).toSphere

/-- The paper's distinguished coordinate on the actual sphere. -/
def coordinate (n : ℕ) (hn : 0 < n) (ω : UnitSphere n) : ℝ := ω.1 ⟨0, hn⟩

theorem coordinate_abs_le_one (n : ℕ) (hn : 0 < n) (ω : UnitSphere n) :
    |coordinate n hn ω| ≤ 1 := by
  have hω : ‖ω.1‖ = (1 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  simpa only [coordinate, Real.norm_eq_abs, hω] using PiLp.norm_apply_le ω.1 ⟨0, hn⟩

/-- The first-coordinate pushforward is supported in the original interval. -/
theorem coordinate_mem_Icc (n : ℕ) (hn : 0 < n) (ω : UnitSphere n) :
    coordinate n hn ω ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := coordinate_abs_le_one n hn ω
  simpa only [Set.mem_Icc, abs_le] using h

theorem continuous_coordinate (n : ℕ) (hn : 0 < n) :
    Continuous (coordinate n hn) := by
  unfold coordinate
  fun_prop

/-- The actual spherical partition function, before normalization. -/
def spherePartition (n : ℕ) (hn : 0 < n) (r : ℝ) : ℝ :=
  ∫ ω : UnitSphere n, Real.exp (r * coordinate n hn ω) ∂area n

/-- The actual spherical first moment, before normalization. -/
def sphereFirstMoment (n : ℕ) (hn : 0 < n) (r : ℝ) : ℝ :=
  ∫ ω : UnitSphere n, coordinate n hn ω * Real.exp (r * coordinate n hn ω) ∂area n

private theorem exp_bound (n : ℕ) (hn : 0 < n) (r : ℝ) (ω : UnitSphere n) :
    Real.exp (r * coordinate n hn ω) ≤ Real.exp |r| := by
  apply Real.exp_le_exp.mpr
  calc
    r * coordinate n hn ω ≤ |r * coordinate n hn ω| := le_abs_self _
    _ = |r| * |coordinate n hn ω| := abs_mul _ _
    _ ≤ |r| * 1 :=
      mul_le_mul_of_nonneg_left (coordinate_abs_le_one n hn ω) (abs_nonneg r)
    _ = |r| := mul_one _

theorem spherePartition_integrable (n : ℕ) (hn : 0 < n) (r : ℝ) :
    Integrable (fun ω : UnitSphere n => Real.exp (r * coordinate n hn ω)) (area n) := by
  letI : IsFiniteMeasure (area n) := by
    change IsFiniteMeasure (volume : Measure (Ambient n)).toSphere
    infer_instance
  have hc : Continuous (fun ω : UnitSphere n => r * coordinate n hn ω) :=
    continuous_const.mul (continuous_coordinate n hn)
  have he : Continuous (fun ω : UnitSphere n => Real.exp (r * coordinate n hn ω)) :=
    Real.continuous_exp.comp hc
  apply Integrable.of_bound he.aestronglyMeasurable (Real.exp |r|)
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    exp_bound n hn r ω

theorem sphereFirstMoment_integrable (n : ℕ) (hn : 0 < n) (r : ℝ) :
    Integrable (fun ω : UnitSphere n =>
      coordinate n hn ω * Real.exp (r * coordinate n hn ω)) (area n) := by
  letI : IsFiniteMeasure (area n) := by
    change IsFiniteMeasure (volume : Measure (Ambient n)).toSphere
    infer_instance
  have hc : Continuous (fun ω : UnitSphere n => r * coordinate n hn ω) :=
    continuous_const.mul (continuous_coordinate n hn)
  have he : Continuous (fun ω : UnitSphere n => Real.exp (r * coordinate n hn ω)) :=
    Real.continuous_exp.comp hc
  apply Integrable.of_bound ((continuous_coordinate n hn).mul he).aestronglyMeasurable
    (Real.exp |r|)
  filter_upwards [] with ω
  change |coordinate n hn ω * Real.exp (r * coordinate n hn ω)| ≤ Real.exp |r|
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |coordinate n hn ω| * Real.exp (r * coordinate n hn ω) ≤
        1 * Real.exp (r * coordinate n hn ω) :=
      mul_le_mul_of_nonneg_right (coordinate_abs_le_one n hn ω)
        (Real.exp_pos _).le
    _ = Real.exp (r * coordinate n hn ω) := one_mul _
    _ ≤ Real.exp |r| := exp_bound n hn r ω

theorem spherePartition_pos (n : ℕ) (hn : 0 < n) (r : ℝ) :
    0 < spherePartition n hn r := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  haveI : NeZero (area n) := ⟨by
    change (volume : Measure (Ambient n)).toSphere ≠ 0
    exact Measure.toSphere_ne_zero _⟩
  exact integral_exp_pos (spherePartition_integrable n hn r)

/-- The true first-coordinate law, obtained by pushforward from the actual
spherical area measure. No beta density is built into this definition. -/
def coordinateLaw (n : ℕ) (hn : 0 < n) : Measure ℝ :=
  (area n).map (coordinate n hn)

theorem coordinateLaw_outside_Icc (n : ℕ) (hn : 0 < n) :
    coordinateLaw n hn (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [coordinateLaw, Measure.map_apply (continuous_coordinate n hn).measurable
    measurableSet_Icc.compl]
  have hpre : coordinate n hn ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ = ∅ := by
    ext ω
    simp [coordinate_mem_Icc n hn ω]
  simp [hpre]

theorem spherePartition_eq_coordinateLaw_integral (n : ℕ) (hn : 0 < n) (r : ℝ) :
    spherePartition n hn r =
      ∫ t : ℝ, Real.exp (r * t) ∂coordinateLaw n hn := by
  rw [spherePartition, coordinateLaw,
    integral_map_of_stronglyMeasurable (continuous_coordinate n hn).measurable
      (by fun_prop)]

theorem sphereFirstMoment_eq_coordinateLaw_integral (n : ℕ) (hn : 0 < n) (r : ℝ) :
    sphereFirstMoment n hn r =
      ∫ t : ℝ, t * Real.exp (r * t) ∂coordinateLaw n hn := by
  rw [sphereFirstMoment, coordinateLaw,
    integral_map_of_stronglyMeasurable (continuous_coordinate n hn).measurable
      (by fun_prop)]

end

end DFL.Geometry
