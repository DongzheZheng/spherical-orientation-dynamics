import DFL.Spectral.RayleighDenominator

/-!
# Quantitative comparison of the physical vMF measures

The bounds hold on the entire original sphere. They apply to every
nonnegative Dirichlet integrand, independently of a harmonic-sector split.
-/

namespace DFL.Spectral

open MeasureTheory

noncomputable section

private theorem alignedMeasure_eq_tilted_zero (d : ℕ) (r : ℝ) :
    alignedMeasure d r =
      (alignedMeasure d 0).tilted (fun x => r * fieldCoordinate d x) := by
  have hzero : Integrable (fun _ : SpherePoint d => Real.exp (0 : ℝ))
      (surfaceMeasure d) := by
    convert fieldWeight_integrable d 0 using 1
    funext x
    simp [fieldWeight]
  have h := tilted_tilted (μ := surfaceMeasure d) hzero
    (fun x => r * fieldCoordinate d x)
  have hfun : ((fun _ : SpherePoint d => (0 : ℝ)) +
      fun x => r * fieldCoordinate d x) =
      (fun x => r * fieldCoordinate d x) := by
    funext x
    simp
  rw [hfun] at h
  simpa [alignedMeasure] using h.symm

private theorem tilt_partition_bounds (d : ℕ) (r : ℝ) :
    Real.exp (-|r|) ≤
      (∫ x : SpherePoint d, Real.exp (r * fieldCoordinate d x)
        ∂alignedMeasure d 0) ∧
      (∫ x : SpherePoint d, Real.exp (r * fieldCoordinate d x)
        ∂alignedMeasure d 0) ≤ Real.exp |r| := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  have hi : Integrable (fun x : SpherePoint d =>
      Real.exp (r * fieldCoordinate d x)) (alignedMeasure d 0) := by
    apply Integrable.of_bound (fieldWeight_continuous d r).aestronglyMeasurable
      (Real.exp |r|)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (fieldWeight_pos d r x)]
      exact (fieldWeight_bounds d r x).2)
  constructor
  · calc
      Real.exp (-|r|) =
          ∫ _x : SpherePoint d, Real.exp (-|r|) ∂alignedMeasure d 0 := by simp
      _ ≤ ∫ x : SpherePoint d, Real.exp (r * fieldCoordinate d x)
          ∂alignedMeasure d 0 :=
        integral_mono (integrable_const _) hi
          (fun x => (fieldWeight_bounds d r x).1)
  · calc
      (∫ x : SpherePoint d, Real.exp (r * fieldCoordinate d x)
          ∂alignedMeasure d 0) ≤
          ∫ _x : SpherePoint d, Real.exp |r| ∂alignedMeasure d 0 :=
        integral_mono hi (integrable_const _)
          (fun x => (fieldWeight_bounds d r x).2)
      _ = Real.exp |r| := by simp

private theorem tilt_density_bounds (d : ℕ) (r : ℝ) (x : SpherePoint d) :
    Real.exp (-2 * |r|) ≤
      Real.exp (r * fieldCoordinate d x) /
        (∫ y : SpherePoint d, Real.exp (r * fieldCoordinate d y)
          ∂alignedMeasure d 0) ∧
      Real.exp (r * fieldCoordinate d x) /
        (∫ y : SpherePoint d, Real.exp (r * fieldCoordinate d y)
          ∂alignedMeasure d 0) ≤ Real.exp (2 * |r|) := by
  let Z : ℝ := ∫ y : SpherePoint d,
    Real.exp (r * fieldCoordinate d y) ∂alignedMeasure d 0
  have hZ := tilt_partition_bounds d r
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZ.1
  have hx := fieldWeight_bounds d r x
  constructor
  · apply (le_div_iff₀ hZpos).2
    calc
      Real.exp (-2 * |r|) * Z ≤
          Real.exp (-2 * |r|) * Real.exp |r| :=
        mul_le_mul_of_nonneg_left hZ.2 (Real.exp_pos _).le
      _ = Real.exp (-|r|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (r * fieldCoordinate d x) := hx.1
  · apply (div_le_iff₀ hZpos).2
    calc
      Real.exp (r * fieldCoordinate d x) ≤ Real.exp |r| := hx.2
      _ = Real.exp (2 * |r|) * Real.exp (-|r|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (2 * |r|) * Z :=
        mul_le_mul_of_nonneg_left hZ.1 (Real.exp_pos _).le

/-- The normalized physical sphere law at field `r` lies between explicit
scalar multiples of the normalized zero-field law, as *whole measures*.
The comparison factor is `exp(2|r|)` in both directions. -/
theorem alignedMeasure_bounds (d : ℕ) (r : ℝ) :
    ENNReal.ofReal (Real.exp (-2 * |r|)) • alignedMeasure d 0 ≤
      alignedMeasure d r ∧
    alignedMeasure d r ≤
      ENNReal.ofReal (Real.exp (2 * |r|)) • alignedMeasure d 0 := by
  rw [alignedMeasure_eq_tilted_zero d r]
  constructor
  · rw [Measure.tilted, ← withDensity_const]
    apply withDensity_mono
    exact ae_of_all _ (fun x =>
      ENNReal.ofReal_le_ofReal (tilt_density_bounds d r x).1)
  · rw [Measure.tilted, ← withDensity_const]
    apply withDensity_mono
    exact ae_of_all _ (fun x =>
      ENNReal.ofReal_le_ofReal (tilt_density_bounds d r x).2)

/-- Every nonnegative integrable observable on the *whole* physical sphere
has quantitatively comparable expectations at finite field and zero field. -/
theorem aligned_integral_bounds (d : ℕ) (r : ℝ)
    (g : SpherePoint d → ℝ)
    (hg0 : Integrable g (alignedMeasure d 0))
    (hgr : Integrable g (alignedMeasure d r))
    (hgpos : ∀ x, 0 ≤ g x) :
    Real.exp (-2 * |r|) * (∫ x, g x ∂alignedMeasure d 0) ≤
      ∫ x, g x ∂alignedMeasure d r ∧
    (∫ x, g x ∂alignedMeasure d r) ≤
      Real.exp (2 * |r|) * (∫ x, g x ∂alignedMeasure d 0) := by
  have hmeas := alignedMeasure_bounds d r
  constructor
  · have h := integral_mono_measure hmeas.1
      (ae_of_all _ (fun x => hgpos x)) hgr
    rw [integral_smul_measure] at h
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using h
  · have h0 : Integrable g
        (ENNReal.ofReal (Real.exp (2 * |r|)) • alignedMeasure d 0) := by
      exact hg0.smul_measure (by simp)
    have h := integral_mono_measure hmeas.2
      (ae_of_all _ (fun x => hgpos x)) h0
    rw [integral_smul_measure] at h
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using h

/-- Every physical `L²` observable at zero field belongs to `L²` at each
finite field strength. This supplies the fixed full-sphere denominator
domain used in the spectral variational problem. -/
theorem memLp_aligned_of_zero (d : ℕ) (r : ℝ)
    (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d 0)) :
    MemLp f 2 (alignedMeasure d r) := by
  have h := (alignedMeasure_bounds d r).2
  exact (hf.smul_measure (by simp)).mono_measure h

/-- The variance of every `L²` function on the original whole sphere is
quantitatively comparable at finite field and zero field. Both inequalities
use variance as the exact optimal subtraction of a constant. -/
theorem sphereVariance_bounds (d : ℕ) (r : ℝ)
    (f : SpherePoint d → ℝ)
    (hf0 : MemLp f 2 (alignedMeasure d 0)) :
    Real.exp (-2 * |r|) * sphereVariance d 0 f ≤ sphereVariance d r f ∧
    sphereVariance d r f ≤
      Real.exp (2 * |r|) * sphereVariance d 0 f := by
  letI : IsProbabilityMeasure (alignedMeasure d 0) :=
    alignedMeasure_probability d 0
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  have hfr := memLp_aligned_of_zero d r f hf0
  constructor
  · let mr : ℝ := ∫ x, f x ∂alignedMeasure d r
    have h0 : Integrable (fun x => (f x - mr) ^ 2)
        (alignedMeasure d 0) := by
      convert (hf0.sub (memLp_const mr)).integrable_sq using 1
    have hr : Integrable (fun x => (f x - mr) ^ 2)
        (alignedMeasure d r) := by
      convert (hfr.sub (memLp_const mr)).integrable_sq using 1
    have hb := aligned_integral_bounds d r
      (fun x => (f x - mr) ^ 2) h0 hr (fun x => sq_nonneg _)
    calc
      Real.exp (-2 * |r|) * sphereVariance d 0 f ≤
          Real.exp (-2 * |r|) *
            (∫ x, (f x - mr) ^ 2 ∂alignedMeasure d 0) :=
        mul_le_mul_of_nonneg_left
          (sphereVariance_le_const_subtraction d 0 f mr hf0)
          (Real.exp_pos _).le
      _ ≤ ∫ x, (f x - mr) ^ 2 ∂alignedMeasure d r := hb.1
      _ = sphereVariance d r f := by
        rw [sphere_const_subtraction_identity d r f mr hfr]
        simp [mr]
  · let m0 : ℝ := ∫ x, f x ∂alignedMeasure d 0
    have h0 : Integrable (fun x => (f x - m0) ^ 2)
        (alignedMeasure d 0) := by
      convert (hf0.sub (memLp_const m0)).integrable_sq using 1
    have hr : Integrable (fun x => (f x - m0) ^ 2)
        (alignedMeasure d r) := by
      convert (hfr.sub (memLp_const m0)).integrable_sq using 1
    have hb := aligned_integral_bounds d r
      (fun x => (f x - m0) ^ 2) h0 hr (fun x => sq_nonneg _)
    calc
      sphereVariance d r f ≤
          ∫ x, (f x - m0) ^ 2 ∂alignedMeasure d r :=
        sphereVariance_le_const_subtraction d r f m0 hfr
      _ ≤ Real.exp (2 * |r|) *
          (∫ x, (f x - m0) ^ 2 ∂alignedMeasure d 0) := hb.2
      _ = Real.exp (2 * |r|) * sphereVariance d 0 f := by
        rw [sphere_const_subtraction_identity d 0 f m0 hf0]
        simp [m0]
end

end DFL.Spectral
