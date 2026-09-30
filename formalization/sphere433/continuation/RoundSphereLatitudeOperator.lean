import DFLSphere433.RoundSphereCoordinates
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

/-! The original latitude differential expression, computed from the
actual round metric and Levi-Civita Laplacian by the scalar chain rule. -/

noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLSpectralCoordinates

namespace DFLLatitudeOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in
/-- The actual latitude gradient has squared norm `1-t²`. -/
theorem latitude_gradient_norm_sq (axis : E) (haxis : ‖axis‖ = 1)
    (x : sphere (0 : E) 1) :
    (roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) axis) x)
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) axis) x) =
      1 - ⟪axis, (x : E)⟫_ℝ^2 := by
  rw [roundMetric_inner]
  change ⟪dIncl (n := n) x (gradFun (roundMetric (E := E) (n := n))
      (innerCoordFun (n := n) axis) x),
    dIncl (n := n) x (gradFun (roundMetric (E := E) (n := n))
      (innerCoordFun (n := n) axis) x)⟫_ℝ = _
  rw [dIncl_coordinate_gradient]
  have haa : ⟪axis, axis⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, haxis]; norm_num
  have hxx : ⟪(x : E), (x : E)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]; norm_num
  have hxa : ⟪(x : E), axis⟫_ℝ = ⟪axis, (x : E)⟫_ℝ := real_inner_comm _ _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, haa, hxx, hxa]
  ring

variable [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- The smooth sphere latitude reduction is the original Sturm--Liouville
expression; no separation formula is supplied as a hypothesis. -/
theorem latitude_laplacian (axis : E) (haxis : ‖axis‖ = 1)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (x : sphere (0 : E) 1) :
    laplacian (LeviCivita (roundMetric (E := E) (n := n)))
      (roundMetric (E := E) (n := n))
      (fun y : sphere (0 : E) 1 => v ⟪axis, (y : E)⟫_ℝ) x =
      (1 - ⟪axis, (x : E)⟫_ℝ^2) * deriv (deriv v) ⟪axis, (x : E)⟫_ℝ -
        (n : ℝ) * ⟪axis, (x : E)⟫_ℝ * deriv v ⟪axis, (x : E)⟫_ℝ := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (E := E) (n := n) axis
  have hgrad := (gradientFun_contMDiffAt_one g (x₀ := x)
    (t.contMDiff.contMDiffAt.of_le (by decide))).mdifferentiableAt (by norm_num)
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hchain := laplacian_comp (LeviCivita g) g
    (hv.differentiable (by norm_num))
    (hv1.differentiable (by norm_num) (t x))
    (fun y => t.contMDiff.mdifferentiableAt (by simp) (x := y)) hgrad
  have hcoord : laplacian (LeviCivita g) g (t : sphere (0 : E) 1 → ℝ) x =
      -(n : ℝ) * ⟪axis, (x : E)⟫_ℝ := by
    calc
      _ = ΔG g t x := laplacian_levi_eq g t.contMDiff x
      _ = _ := coordinate_laplacian x axis
  have hnorm := latitude_gradient_norm_sq (n := n) axis haxis x
  rw [hcoord, hnorm] at hchain
  change laplacian (LeviCivita g) g (fun y : sphere (0 : E) 1 => v (t y)) x = _
  rw [hchain]
  change deriv v (⟪axis, (x : E)⟫_ℝ) * (-(n : ℝ) * ⟪axis, (x : E)⟫_ℝ) +
    deriv (deriv v) (⟪axis, (x : E)⟫_ℝ) * (1 - ⟪axis, (x : E)⟫_ℝ^2) = _
  ring

omit [FiniteDimensional ℝ E] in
/-- An actual smooth sphere eigenfunction represented by a C² latitude
profile satisfies the manuscript's original profile equation. -/
theorem latitude_schrodinger_equation (axis : E) (haxis : ‖axis‖ = 1)
    (F v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hu : ∀ x, u x = v (⟪axis, (x : E)⟫_ℝ)) (lam : ℝ)
    (heig : ∀ x, -ΔG (roundMetric (E := E) (n := n)) u x +
      F (⟪axis, (x : E)⟫_ℝ) * u x = lam * u x) (x : sphere (0 : E) 1) :
    -(1 - ⟪axis, (x : E)⟫_ℝ^2) * deriv (deriv v) (⟪axis, (x : E)⟫_ℝ) +
      (n : ℝ) * ⟪axis, (x : E)⟫_ℝ * deriv v (⟪axis, (x : E)⟫_ℝ) +
      F (⟪axis, (x : E)⟫_ℝ) * v (⟪axis, (x : E)⟫_ℝ) =
      lam * v (⟪axis, (x : E)⟫_ℝ) := by
  let g := roundMetric (E := E) (n := n)
  have hufun : (u : sphere (0 : E) 1 → ℝ) =
      fun y : sphere (0 : E) 1 => v ⟪axis, (y : E)⟫_ℝ := funext hu
  have hLap : ΔG g u x =
      (1 - ⟪axis, (x : E)⟫_ℝ^2) * deriv (deriv v) (⟪axis, (x : E)⟫_ℝ) -
        (n : ℝ) * ⟪axis, (x : E)⟫_ℝ * deriv v (⟪axis, (x : E)⟫_ℝ) := by
    calc
      _ = laplacian (LeviCivita g) g (u : sphere (0 : E) 1 → ℝ) x :=
        (laplacian_levi_eq g u.contMDiff x).symm
      _ = laplacian (LeviCivita g) g
          (fun y : sphere (0 : E) 1 => v ⟪axis, (y : E)⟫_ℝ) x := by rw [hufun]
      _ = _ := latitude_laplacian axis haxis v hv x
  have hh := heig x
  rw [hLap, hu x] at hh
  linarith

end DFLLatitudeOperator
