import DifferentialGeometry.Geometry.Metric.Sphere.Round.Shape
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity

/-! Coordinate eigenfunctions of the actual unit round sphere.
The ambient inclusion, induced round metric, Levi-Civita connection,
Hessian, and chart-volume scalar Laplace--Beltrami operator are the
upstream geometric objects. No coordinate eigen-equation is assumed. -/

noncomputable section
open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

namespace DFLSpectralCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The genuine ambient representative of the geometric coordinate gradient. -/
theorem dIncl_coordinate_gradient (x : sphere (0 : E) 1) (w : E) :
    dIncl (n := n) x (gradFun (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) x) =
      w - ⟪w, (x : E)⟫ • (x : E) := by
  let u : ((ℝ ∙ (x : E))ᗮ) := ((ℝ ∙ (x : E))ᗮ).orthogonalProjectionOnto w
  let z : TangentSpace (𝓡 n) x := (dInclEquiv (n := n) x).symm u
  have hz : dIncl (n := n) x z = (u : E) := by
    rw [← dInclEquiv_coe (n := n) x]
    exact congrArg Subtype.val ((dInclEquiv (n := n) x).apply_symm_apply u)
  have hg : z = gradFun (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) x := by
    apply gradFun_unique
    intro a
    rw [roundMetric_inner, hz, mfderiv_innerCoordFun]
    have ha : ((dInclEquiv (n := n) x a : ((ℝ ∙ (x : E))ᗮ)) : E) = dIncl (n := n) x a :=
      dInclEquiv_coe (n := n) x a
    rw [← ha]
    exact ((ℝ ∙ (x : E))ᗮ).inner_orthogonalProjectionOnto_eq_of_mem_right
      (dInclEquiv (n := n) x a) w
  rw [← hg, hz]
  change (↑(((ℝ ∙ (x : E))ᗮ).orthogonalProjectionOnto w) : E) = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  have hsing : (ℝ ∙ (x : E)).starProjection w = ⟪(x : E), w⟫ • (x : E) :=
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x) w
  have hsplit := (ℝ ∙ (x : E)).starProjection_add_starProjection_orthogonal w
  rw [hsing, real_inner_comm w (x : E)] at hsplit
  exact eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)

omit [FiniteDimensional ℝ E] [NeZero n] in
private theorem ambient_coordinate_gradient_derivative (x : sphere (0 : E) 1)
    (w : E) (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (fun p => gradFun (I := 𝓡 n)
      (roundMetric (E := E) (n := n)) (innerCoordFun (E := E) (n := n) w) p) x v =
      -(⟪w, dIncl (n := n) x v⟫ • (x : E) + ⟪w, (x : E)⟫ • dIncl (n := n) x v) := by
  let f : sphere (0 : E) 1 → ℝ := innerCoordFun (E := E) (n := n) w
  have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x :=
    (innerCoordFun (E := E) (n := n) w).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hiC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hi : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hiC.mdifferentiableAt (by simp)
  have hfun : dInclField (n := n) (fun p => gradFun (I := 𝓡 n)
      (roundMetric (E := E) (n := n)) f p) = fun p => w - f p • (p : E) := by
    funext p
    rw [dInclField_apply, dIncl_coordinate_gradient]
    rfl
  rw [ambDeriv_apply, hfun]
  change (mvfderiv (𝓡 n) ((fun _ : sphere (0 : E) 1 => w) -
    f • ((↑) : sphere (0 : E) 1 → E)) x) v = _
  rw [mvfderiv_sub (mdifferentiableAt_const) (hf.smul hi), mvfderiv_const,
    mvfderiv_smul hf hi]
  simp only [zero_sub]
  change -(f x • dIncl (n := n) x v + (mvfderiv (𝓡 n) f x v) • (x : E)) = _
  have hdf : mvfderiv (𝓡 n) f x v = ⟪w, dIncl (n := n) x v⟫ := by
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    have hraw := mfderiv_innerCoordFun (E := E) (n := n) w x v
    have h := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ)
      ((innerCoordFun (E := E) (n := n) w) x)) hraw
    with_unfolding_all exact h
  rw [hdf]
  change -(⟪w, (x : E)⟫ • dIncl (n := n) x v + ⟪w, dIncl (n := n) x v⟫ • (x : E)) = _
  rw [add_comm]

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The coordinate Hessian is exactly minus the coordinate times the round metric. -/
theorem coordinate_hessian (x : sphere (0 : E) 1) (w : E)
    (v z : TangentSpace (𝓡 n) x) :
    abstractHessian (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) x v z =
      -⟪w, (x : E)⟫ * (roundMetric (E := E) (n := n)).inner x v z := by
  have hg : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p
        (gradFun (I := 𝓡 n) (roundMetric (E := E) (n := n))
          (innerCoordFun (E := E) (n := n) w) p)) x :=
    (gradFun_contMDiff_total_section (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w).contMDiff x).mdifferentiableAt (by simp)
  rw [← abstractHessian_eq_inner_cov_gradFun_extend (I := 𝓡 n)
    (roundMetric (E := E) (n := n)) (innerCoordFun (E := E) (n := n) w).contMDiff]
  change ⟪dIncl (n := n) x (metricCov (roundMetric (E := E) (n := n))
    (fun p => gradFun (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) p) x v), dIncl (n := n) x z⟫ = _
  rw [inner_dIncl_metricCov hg v z, ambient_coordinate_gradient_derivative]
  have hz : ⟪(x : E), dIncl (n := n) x z⟫ = 0 := by
    apply Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_span_singleton_self (x : E))
    rw [← range_mvfderiv_subtypeVal (n := n) x]
    exact ⟨z, rfl⟩
  rw [inner_neg_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    hz, mul_zero, zero_add, roundMetric_inner]
  ring

omit [FiniteDimensional ℝ E] in
/-- Every ambient linear coordinate is an actual eigenfunction of the
unit-round-sphere Laplace--Beltrami operator, with eigenvalue minus n. -/
theorem coordinate_laplacian (x : sphere (0 : E) 1) (w : E) :
    ΔG (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) x = -(n : ℝ)*⟪w, (x : E)⟫ := by
  change ΔG (I := 𝓡 n) (roundMetric (E := E) (n := n))
    ⟨_, (innerCoordFun (E := E) (n := n) w).contMDiff⟩ x = _
  rw [← sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := 𝓡 n)
    (roundMetric (E := E) (n := n)) (innerCoordFun (E := E) (n := n) w).contMDiff]
  simp only [coordinate_hessian, smoothOrthoFrame_orthonormal_at_center, if_true, mul_one]
  simp

end DFLSpectralCoordinates

#print axioms DFLSpectralCoordinates.dIncl_coordinate_gradient
#print axioms DFLSpectralCoordinates.coordinate_hessian
#print axioms DFLSpectralCoordinates.coordinate_laplacian
