import continuation.SeparatedGradient

/-! Actual angular slices and latitude derivatives in the product
Dirichlet density, following the original coordinate separation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold Metric Module
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
namespace DFLProductSlices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The actual full product gradient consists of the angular slice
gradient and the ordinary real latitude derivative. -/
theorem product_gradient_slices (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (x : M × ℝ) :
    gradFun (h.prod (euclideanMetric (E := ℝ))) F x =
      (gradFun h (fun y : M => F (y,x.2)) x.1,
        deriv (fun s : ℝ => F (x.1,s)) x.2) := by
  symm
  apply Connection.gradFun_unique
  intro v
  have hp := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
    (g := h) (h := euclideanMetric (E := ℝ)) (x := x)
    (gradFun h (fun y : M => F (y,x.2)) x.1,
      deriv (fun s : ℝ => F (x.1,s)) x.2) v
  change (h.prod (euclideanMetric (E := ℝ))).inner x _ v =
    h.inner x.1 (gradFun h (fun y : M => F (y,x.2)) x.1) v.1+
    inner ℝ (deriv (fun s : ℝ => F (x.1,s)) x.2) v.2 at hp
  rw [hp,Connection.gradFun_metricDual,Real.inner_apply]
  rw [mfderiv_prod_eq_add_apply (F.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  congr 1
  exact (fderiv_eq_deriv_mul (f := fun s : ℝ => F (x.1,s)) (x := x.2) (y := v.2)).symm

/-- The original separated pointwise energy, now in actual angular
slice gradients and ordinary latitude derivatives. -/
theorem separated_gradient_energy_slices
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (x : M × ℝ) :
    normGradSqFun gP F x =
      ((f x.2)^2)⁻¹*normGradSqFun h (fun y : M => F (y,x.2)) x.1+
        ((b x.2)^2)⁻¹*(deriv (fun s : ℝ => F (x.1,s)) x.2)^2 := by
  rw [DFLSeparatedGradient.separated_gradient_energy h gP f b hf hb hsep F x,
    product_gradient_slices h F x,normGradSqFun_def]

end DFLProductSlices
