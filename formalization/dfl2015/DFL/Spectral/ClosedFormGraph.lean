import DFL.Spectral.WholeSphereGap

/-!
# The completed graph of the original smooth spherical Dirichlet form

For each fixed field, we place a smooth spherical test and its true tangent
gradient in the product of two `L²` spaces over the physical vMF law. The
closure of this graph is a complete metric form domain. Its identification
with the paper's classical weak-gradient `H¹(Sᵈ)` is not asserted here.
-/

namespace DFL.Spectral

open MeasureTheory Metric InnerProductSpace

noncomputable section

private theorem norm_toLp_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    (g : α → E) (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  let u : Lp E 2 μ := hg.toLp g
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ x, inner ℝ (u x) (u x) ∂μ := L2.inner_def u u
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by
      simp_rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, ‖g x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]

/-- The centered value of a smooth ambient extension on the physical
sphere. Centering is with respect to the actual field-dependent law. -/
def centeredCoreValue (d : ℕ) (r : ℝ) (f : SphereC1Core d)
    (x : SpherePoint d) : ℝ :=
  coreValue d f x - ∫ y, coreValue d f y ∂alignedMeasure d r

theorem centeredCoreValue_memLp (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    MemLp (centeredCoreValue d r f) 2 (alignedMeasure d r) := by
  letI : IsProbabilityMeasure (alignedMeasure d r) :=
    alignedMeasure_probability d r
  exact (coreValue_memLp d r f).sub
    (memLp_const (∫ y, coreValue d f y ∂alignedMeasure d r))

theorem coreTangentGradient_memLp (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    MemLp (coreTangentGradient d f) 2 (alignedMeasure d r) := by
  apply (memLp_two_iff_integrable_sq_norm
    (coreTangentGradient_continuous d f).aestronglyMeasurable).2
  exact coreEnergy_integrable d r f

/-- Exact centered function/gradient graph in the ambient product of the
physical spherical `L²` spaces. -/
def coreGraph (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    Lp ℝ 2 (alignedMeasure d r) × Lp (Ambient d) 2 (alignedMeasure d r) :=
  ⟨(centeredCoreValue_memLp d r f).toLp (centeredCoreValue d r f),
    (coreTangentGradient_memLp d r f).toLp (coreTangentGradient d f)⟩

/-- On each smooth test, the first `L²` norm squared is exactly the
original Rayleigh variance denominator. -/
theorem coreGraph_value_norm_sq (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    ‖(coreGraph d r f).1‖ ^ 2 =
      sphereVariance d r (coreValue d f) := by
  rw [coreGraph, norm_toLp_sq_eq_integral_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs, centeredCoreValue]
  exact (sphereVariance_eq_integral d r (coreValue d f)
    (coreValue_memLp d r f)).symm

/-- On each smooth test, the second `L²` norm squared is exactly the
original intrinsic Dirichlet energy. -/
theorem coreGraph_gradient_norm_sq (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    ‖(coreGraph d r f).2‖ ^ 2 = coreEnergy d r f := by
  rw [coreGraph, norm_toLp_sq_eq_integral_norm_sq]
  rfl

/-- The metric closure of the actual smooth form graph in the product of
the original physical sphere's value and tangent-gradient `L²` spaces. -/
def closedFormGraph (d : ℕ) (r : ℝ) :
    Set (Lp ℝ 2 (alignedMeasure d r) ×
      Lp (Ambient d) 2 (alignedMeasure d r)) :=
  closure (Set.range (coreGraph d r))

/-- The graph completion as a subtype of a complete product of `L²`
spaces. This construction retains both value and gradient components. -/
abbrev ClosedFormSpace (d : ℕ) (r : ℝ) :=
  {p : Lp ℝ 2 (alignedMeasure d r) ×
      Lp (Ambient d) 2 (alignedMeasure d r) // p ∈ closedFormGraph d r}

instance closedFormSpace_complete (d : ℕ) (r : ℝ) :
    CompleteSpace (ClosedFormSpace d r) := by
  unfold ClosedFormSpace closedFormGraph
  letI : IsClosed (closure
      (Set.range (coreGraph d r) :
        Set (Lp ℝ 2 (alignedMeasure d r) ×
          Lp (Ambient d) 2 (alignedMeasure d r)))) := isClosed_closure
  infer_instance

end

end DFL.Spectral
