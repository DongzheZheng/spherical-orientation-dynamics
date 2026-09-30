import continuation.WarpedProductVolume
import DifferentialGeometry.Geometry.Operator.Product

/-! The manuscript's angular/latitude energy splitting follows from
actual gradient duality for the separated metric. No gradient formula
or energy decomposition is assumed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
namespace DFLSeparatedGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Actual inverse angular/line metric factors in the gradient. -/
theorem separated_gradient
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (x : M × ℝ) :
    gradFun gP F x =
      (((f x.2)^2)⁻¹ • (gradFun (h.prod (euclideanMetric (E := ℝ))) F x).1,
        ((b x.2)^2)⁻¹ * (gradFun (h.prod (euclideanMetric (E := ℝ))) F x).2) := by
  let q := h.prod (euclideanMetric (E := ℝ))
  let A := gradFun q F x
  let z : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x :=
    (((f x.2)^2)⁻¹ • A.1,((b x.2)^2)⁻¹*A.2)
  have hz : z = gradFun gP F x := by
    apply Connection.gradFun_unique
    intro v
    have hh := hsep x.1 x.2 z.1 v.1 z.2 v.2
    change gP.inner x z v = _ at hh
    rw [hh]
    have hq := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
      (g := h) (h := euclideanMetric (E := ℝ)) (x := x) A v
    change q.inner x A v = h.inner x.1 A.1 v.1+inner ℝ A.2 v.2 at hq
    rw [Real.inner_apply] at hq
    calc
      _ = h.inner x.1 A.1 v.1+A.2*v.2 := by
        dsimp only [z]
        simp only [map_smul,smul_apply,smul_eq_mul]
        field_simp [ne_of_gt (hf x.2),ne_of_gt (hb x.2)]
      _ = q.inner x A v := hq.symm
      _ = _ := by
        exact Connection.gradFun_metricDual_mvfderiv q F x v
  exact hz.symm

/-- Actual pointwise Dirichlet density splits into the two inverse metric
factors; the angular and line components are those of the true product
gradient. -/
theorem separated_gradient_energy
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (x : M × ℝ) :
    normGradSqFun gP F x =
      ((f x.2)^2)⁻¹*h.inner x.1
        (gradFun (h.prod (euclideanMetric (E := ℝ))) F x).1
        (gradFun (h.prod (euclideanMetric (E := ℝ))) F x).1+
      ((b x.2)^2)⁻¹*((gradFun (h.prod (euclideanMetric (E := ℝ))) F x).2)^2 := by
  rw [normGradSqFun_def,separated_gradient h gP f b hf hb hsep F x]
  let A := gradFun (h.prod (euclideanMetric (E := ℝ))) F x
  have hh := hsep x.1 x.2 (((f x.2)^2)⁻¹ • A.1) (((f x.2)^2)⁻¹ • A.1)
    (((b x.2)^2)⁻¹*A.2) (((b x.2)^2)⁻¹*A.2)
  change gP.inner x _ _ = _ at hh
  rw [hh]
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp [ne_of_gt (hf x.2),ne_of_gt (hb x.2)]
  ring

end DFLSeparatedGradient
