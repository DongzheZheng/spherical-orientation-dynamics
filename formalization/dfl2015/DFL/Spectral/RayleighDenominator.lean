import DFL.Spectral.SphereMeasure

/-!
# The denominator of the original spherical Rayleigh quotient

Everything in this file uses the **same original weighted sphere measure**
`alignedMeasure d r`.  In particular, positivity of the denominator is
proved for actual square-integrable functions of the whole sphere, without
restricting to any angular sector.  The tangential Dirichlet numerator and
its `H¹` form domain are not yet formalized.
-/

namespace DFL.Spectral

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The variance in the original spherical Rayleigh quotient. -/
def sphereVariance (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ) : ℝ :=
  ProbabilityTheory.variance f (alignedMeasure d r)

theorem sphereVariance_nonneg (d : ℕ) (r : ℝ)
    (f : SpherePoint d → ℝ) : 0 ≤ sphereVariance d r f := by
  exact ProbabilityTheory.variance_nonneg f _

/-- For any genuine `L²` function on the original sphere, variance zero is
equivalent to being almost everywhere equal to its own weighted mean. -/
theorem sphereVariance_pos_iff_not_ae_mean
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    0 < sphereVariance d r f ↔
      ¬ f =ᵐ[alignedMeasure d r]
        (fun _ => ∫ x, f x ∂alignedMeasure d r) := by
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  constructor
  · intro hpos hconst
    have hevar0 : ProbabilityTheory.evariance f (alignedMeasure d r) = 0 :=
      (ProbabilityTheory.evariance_eq_zero_iff hf.aemeasurable).2 hconst
    have hvar0 : sphereVariance d r f = 0 := by
      simp [sphereVariance, ProbabilityTheory.variance, hevar0]
    exact (ne_of_gt hpos) hvar0
  · intro hnot
    by_contra hpos
    have hzero : sphereVariance d r f = 0 :=
      le_antisymm (le_of_not_gt hpos) (sphereVariance_nonneg d r f)
    exact hnot (ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hf hzero)

/-- The Rayleigh denominator is positive exactly for nonconstant `L²`
classes on the complete weighted sphere. -/
theorem sphereVariance_pos_iff_not_ae_constant
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    0 < sphereVariance d r f ↔
      ¬ ∃ c : ℝ, f =ᵐ[alignedMeasure d r] fun _ => c := by
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  rw [sphereVariance_pos_iff_not_ae_mean d r f hf]
  constructor
  · intro h ⟨c, hc⟩
    have hmean : (∫ x, f x ∂alignedMeasure d r) = c := by
      rw [integral_congr_ae hc]
      simp
    apply h
    simpa [hmean] using hc
  · intro h hmean
    exact h ⟨∫ x, f x ∂alignedMeasure d r, hmean⟩

/-- The excluded constant functions are the same for every finite field:
the exclusion is about the original sphere, not a field-dependent quotient. -/
theorem ae_constant_aligned_iff_surface
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ) (c : ℝ) :
    f =ᵐ[alignedMeasure d r] (fun _ => c) ↔
      f =ᵐ[surfaceMeasure d] (fun _ => c) := by
  constructor
  · exact (alignedMeasure_equivalent d r).2.ae_eq
  · exact (alignedMeasure_equivalent d r).1.ae_eq

theorem sphereVariance_pos_iff_not_surface_constant
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    0 < sphereVariance d r f ↔
      ¬ ∃ c : ℝ, f =ᵐ[surfaceMeasure d] fun _ => c := by
  rw [sphereVariance_pos_iff_not_ae_constant d r f hf]
  simp only [ae_constant_aligned_iff_surface]

/-- The mean-subtracted `L²` norm squared is exactly the original
Rayleigh denominator. -/
theorem sphereVariance_eq_integral
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    sphereVariance d r f =
      ∫ x, (f x - ∫ y, f y ∂alignedMeasure d r) ^ 2
        ∂alignedMeasure d r := by
  exact ProbabilityTheory.variance_eq_integral hf.aemeasurable

/-- In the exact weighted spherical law, subtracting the weighted mean is
the unique optimal constant subtraction in the `L²` denominator. -/
theorem sphere_const_subtraction_identity
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ) (c : ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    (∫ x, (f x - c) ^ 2 ∂alignedMeasure d r) =
      sphereVariance d r f +
        (c - ∫ x, f x ∂alignedMeasure d r) ^ 2 := by
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  have hsq : Integrable (fun x => (f x) ^ 2) (alignedMeasure d r) :=
    hf.integrable_sq
  have hfint : Integrable f (alignedMeasure d r) :=
    hf.integrable (by norm_num)
  have hvar : sphereVariance d r f =
      (∫ x, (f x) ^ 2 ∂alignedMeasure d r) -
        (∫ x, f x ∂alignedMeasure d r) ^ 2 := by
    simpa [sphereVariance] using ProbabilityTheory.variance_eq_sub hf
  calc
    (∫ x, (f x - c) ^ 2 ∂alignedMeasure d r) =
        ∫ x, ((f x) ^ 2 - (2 * c) * f x + c ^ 2)
          ∂alignedMeasure d r := by
      congr 1
      funext x
      ring
    _ = (∫ x, (f x) ^ 2 ∂alignedMeasure d r) -
        (2 * c) * (∫ x, f x ∂alignedMeasure d r) + c ^ 2 := by
      have hlin : Integrable (fun x => (2 * c) * f x) (alignedMeasure d r) :=
        hfint.const_mul _
      have hsub : Integrable (fun x => (f x) ^ 2 - (2 * c) * f x)
          (alignedMeasure d r) := hsq.sub hlin
      rw [integral_add hsub (integrable_const (c ^ 2)),
        integral_sub hsq hlin, integral_const_mul]
      simp
    _ = sphereVariance d r f +
        (c - ∫ x, f x ∂alignedMeasure d r) ^ 2 := by
      rw [hvar]
      ring

theorem sphereVariance_le_const_subtraction
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ) (c : ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    sphereVariance d r f ≤
      ∫ x, (f x - c) ^ 2 ∂alignedMeasure d r := by
  rw [sphere_const_subtraction_identity d r f c hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem sphere_const_subtraction_eq_variance_iff
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ) (c : ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    (∫ x, (f x - c) ^ 2 ∂alignedMeasure d r) = sphereVariance d r f ↔
      c = ∫ x, f x ∂alignedMeasure d r := by
  rw [sphere_const_subtraction_identity d r f c hf]
  constructor
  · intro h
    have hz : (c - ∫ x, f x ∂alignedMeasure d r) ^ 2 = 0 := by
      linarith
    nlinarith
  · intro h
    rw [h]
    ring

/-- The original spherical Rayleigh denominator is the exact infimum of
`L²` distance squared from constants, attained at the weighted mean. -/
theorem sphereVariance_eq_sInf_const_subtraction
    (d : ℕ) (r : ℝ) (f : SpherePoint d → ℝ)
    (hf : MemLp f 2 (alignedMeasure d r)) :
    sphereVariance d r f =
      sInf (Set.range (fun c : ℝ =>
        ∫ x, (f x - c) ^ 2 ∂alignedMeasure d r)) := by
  have hleast : IsLeast
      (Set.range (fun c : ℝ =>
        ∫ x, (f x - c) ^ 2 ∂alignedMeasure d r))
      (sphereVariance d r f) := by
    constructor
    · refine ⟨∫ x, f x ∂alignedMeasure d r, ?_⟩
      dsimp only
      rw [sphere_const_subtraction_identity d r f _ hf]
      ring
    · intro z hz
      rcases hz with ⟨c, rfl⟩
      exact sphereVariance_le_const_subtraction d r f c hf
  exact hleast.csInf_eq.symm

end

end DFL.Spectral
