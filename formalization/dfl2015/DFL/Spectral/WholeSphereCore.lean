import DFL.Spectral.WeightedMeasureComparison

/-!
# The physical whole-sphere smooth Dirichlet form

The core consists of restrictions of ambient `C¹` functions to the actual
unit sphere. Its gradient is projected onto the sphere's tangent space.
This is a global core; no latitude or harmonic-sector restriction occurs.
The completion to the paper's full `H¹(Sᵈ)` remains a separate theorem.
-/

namespace DFL.Spectral

open MeasureTheory Metric InnerProductSpace

noncomputable section

/-- Restrictions of ambient `C¹` functions to the physical sphere. -/
structure SphereC1Core (d : ℕ) where
  toFun : Ambient d → ℝ
  smooth : ContDiff ℝ 1 toFun

/-- The value of an ambient `C¹` test function on the original sphere. -/
def coreValue (d : ℕ) (f : SphereC1Core d) (x : SpherePoint d) : ℝ :=
  f.toFun x.1

/-- The actual tangent projection of the ambient gradient. -/
def coreTangentGradient (d : ℕ) (f : SphereC1Core d)
    (x : SpherePoint d) : Ambient d :=
  gradient f.toFun x.1 - (inner ℝ (gradient f.toFun x.1) x.1) • x.1

/-- The projected vector lies in the tangent hyperplane. -/
theorem coreTangentGradient_tangent (d : ℕ) (f : SphereC1Core d)
    (x : SpherePoint d) :
    inner ℝ (coreTangentGradient d f x) x.1 = 0 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  simp [coreTangentGradient, inner_sub_left, real_inner_smul_left, hx]

/-- On every tangent vector, the projected gradient represents the
directional derivative of the restricted physical function. -/
theorem coreTangentGradient_pairing (d : ℕ) (f : SphereC1Core d)
    (x : SpherePoint d) (v : Ambient d)
    (hv : inner ℝ x.1 v = 0) :
    inner ℝ (coreTangentGradient d f x) v =
      fderiv ℝ f.toFun x.1 v := by
  have hdiff : DifferentiableAt ℝ f.toFun x.1 :=
    (f.smooth.differentiable (by norm_num)) x.1
  simp [coreTangentGradient, inner_sub_left, real_inner_smul_left,
    hv, inner_gradient_left hdiff]

theorem coreValue_continuous (d : ℕ) (f : SphereC1Core d) :
    Continuous (coreValue d f) :=
  f.smooth.continuous.comp continuous_subtype_val

theorem coreTangentGradient_continuous (d : ℕ) (f : SphereC1Core d) :
    Continuous (coreTangentGradient d f) := by
  have hgrad : Continuous (gradient f.toFun) := by
    unfold gradient
    exact (toDual ℝ (Ambient d)).symm.continuous.comp
      (f.smooth.continuous_fderiv (by norm_num))
  have hval : Continuous (fun x : SpherePoint d => (x.1 : Ambient d)) :=
    continuous_subtype_val
  have hg : Continuous (fun x : SpherePoint d => gradient f.toFun x.1) :=
    hgrad.comp hval
  exact hg.sub ((hg.inner hval).smul hval)

private theorem integrable_continuous_sphere (d : ℕ) (r : ℝ)
    {g : SpherePoint d → ℝ} (hg : Continuous g) :
    Integrable g (alignedMeasure d r) := by
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  obtain ⟨C, hC⟩ :=
    isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ (fun x => hC x (Set.mem_univ x)))

theorem coreValue_memLp (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    MemLp (coreValue d f) 2 (alignedMeasure d r) := by
  apply (memLp_two_iff_integrable_sq
    (coreValue_continuous d f).aestronglyMeasurable).2
  exact integrable_continuous_sphere d r ((coreValue_continuous d f).pow 2)

/-- The original weighted tangential Dirichlet energy on the complete
sphere, evaluated on an ambient `C¹` test function. -/
def coreEnergy (d : ℕ) (r : ℝ) (f : SphereC1Core d) : ℝ :=
  ∫ x : SpherePoint d, ‖coreTangentGradient d f x‖ ^ 2
    ∂alignedMeasure d r

theorem coreEnergy_integrable (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    Integrable (fun x : SpherePoint d =>
      ‖coreTangentGradient d f x‖ ^ 2) (alignedMeasure d r) :=
  integrable_continuous_sphere d r
    ((coreTangentGradient_continuous d f).norm.pow 2)

/-- The physical Dirichlet energy of every `C¹` test on the original
sphere is comparable across finite field strengths. -/
theorem coreEnergy_bounds (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    Real.exp (-2 * |r|) * coreEnergy d 0 f ≤ coreEnergy d r f ∧
    coreEnergy d r f ≤ Real.exp (2 * |r|) * coreEnergy d 0 f := by
  exact aligned_integral_bounds d r
    (fun x => ‖coreTangentGradient d f x‖ ^ 2)
    (coreEnergy_integrable d 0 f) (coreEnergy_integrable d r f)
    (fun x => sq_nonneg _)

/-- Squared `L²` plus tangential energy on the original smooth core. -/
def coreFormNormSq (d : ℕ) (r : ℝ) (f : SphereC1Core d) : ℝ :=
  (∫ x : SpherePoint d, (coreValue d f x) ^ 2 ∂alignedMeasure d r) +
    coreEnergy d r f

/-- Uniform equivalence of the full-sphere smooth-core form norms for
every finite field. This supplies the quantitative input for identifying
their completions; the completion itself is not asserted here. -/
theorem coreFormNormSq_bounds (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    Real.exp (-2 * |r|) * coreFormNormSq d 0 f ≤ coreFormNormSq d r f ∧
    coreFormNormSq d r f ≤ Real.exp (2 * |r|) * coreFormNormSq d 0 f := by
  have hval := aligned_integral_bounds d r
    (fun x => (coreValue d f x) ^ 2)
    (integrable_continuous_sphere d 0 ((coreValue_continuous d f).pow 2))
    (integrable_continuous_sphere d r ((coreValue_continuous d f).pow 2))
    (fun x => sq_nonneg _)
  have hen := coreEnergy_bounds d r f
  constructor
  · unfold coreFormNormSq
    rw [mul_add]
    exact add_le_add hval.1 hen.1
  · unfold coreFormNormSq
    rw [mul_add]
    exact add_le_add hval.2 hen.2

/-- The global variance denominator of each smooth-core test obeys the
same quantitative field comparison. -/
theorem coreVariance_bounds (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    Real.exp (-2 * |r|) * sphereVariance d 0 (coreValue d f) ≤
      sphereVariance d r (coreValue d f) ∧
    sphereVariance d r (coreValue d f) ≤
      Real.exp (2 * |r|) * sphereVariance d 0 (coreValue d f) :=
  sphereVariance_bounds d r (coreValue d f) (coreValue_memLp d 0 f)

end

end DFL.Spectral
