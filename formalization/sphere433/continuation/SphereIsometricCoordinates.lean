import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Bundle.PartialMfderiv.Composition

/-! Ambient linear isometries give actual round-sphere diffeomorphisms
between different ambient Euclidean spaces, including the complex plane. -/
noncomputable section
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection

namespace DFLSphereIsometric
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = n + 1)]

def sphereLinearMap (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 → sphere (0 : F) 1 :=
  Set.codRestrict (fun x : sphere (0 : E) 1 => e (x : E)) (sphere (0 : F) 1) (fun x => by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.property)

omit [FiniteDimensional ℝ F] in
private theorem sphereLinearMap_smooth (e : E ≃ₗᵢ[ℝ] F) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereLinearMap e) :=
  ContMDiff.codRestrict_sphere
    (e.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _

def sphereLinearDiffeo (e : E ≃ₗᵢ[ℝ] F) :
    sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1 where
  toFun := sphereLinearMap e
  invFun := sphereLinearMap e.symm
  left_inv x := Subtype.ext (by simp [sphereLinearMap])
  right_inv x := Subtype.ext (by simp [sphereLinearMap])
  contMDiff_toFun := sphereLinearMap_smooth e
  contMDiff_invFun := sphereLinearMap_smooth e.symm

theorem dIncl_sphereLinearDiffeo (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    dIncl (n := n) (sphereLinearDiffeo (n := n) e x)
      (mfderiv (𝓡 n) (𝓡 n) (sphereLinearDiffeo (n := n) e) x v) = e (dIncl (n := n) x v) := by
  have h0 : (∞ : ℕ∞ω) ≠ 0 := by decide
  have hιF := (contMDiff_coe_sphere (E := F) (n := n)).mdifferentiableAt h0
    (x := sphereLinearDiffeo (n := n) e x)
  have hΦ := (sphereLinearDiffeo (n := n) e).contMDiff.mdifferentiableAt h0 (x := x)
  have hιE := (contMDiff_coe_sphere (E := E) (n := n)).mdifferentiableAt h0 (x := x)
  have he := e.toContinuousLinearMap.contMDiff.mdifferentiableAt h0 (x := (x : E))
  have h1 := hιF.mvfderiv_comp_apply hΦ v
  have h2 := he.mvfderiv_comp_apply hιE v
  have hcomp : ((↑) : sphere (0 : F) 1 → F) ∘ sphereLinearDiffeo (n := n) e =
      e.toContinuousLinearMap ∘ ((↑) : sphere (0 : E) 1 → E) := rfl
  rw [hcomp] at h1
  have hL : mvfderiv 𝓘(ℝ, E) e.toContinuousLinearMap (x : E) = e.toContinuousLinearMap := by
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    with_unfolding_all rfl
  rw [hL] at h2
  with_unfolding_all exact h1.symm.trans h2

theorem sphereLinearDiffeo_pullback_round (e : E ≃ₗᵢ[ℝ] F) :
    Diffeomorph.pullbackMetricCross (roundMetric (E := F) (n := n))
      (sphereLinearDiffeo (n := n) e) = roundMetric (E := E) (n := n) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner, roundMetric_inner, roundMetric_inner,
    dIncl_sphereLinearDiffeo, dIncl_sphereLinearDiffeo]
  exact e.inner_map_map _ _

theorem sphereLinearDiffeo_laplacian (e : E ≃ₗᵢ[ℝ] F)
    (f : C^∞⟮𝓡 n, sphere (0 : F) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    ΔG (roundMetric (E := E) (n := n))
      ⟨f ∘ sphereLinearDiffeo (n := n) e, f.contMDiff.comp (sphereLinearDiffeo (n := n) e).contMDiff⟩ x =
        ΔG (roundMetric (E := F) (n := n)) f (sphereLinearDiffeo (n := n) e x) := by
  have hnat := laplacian_pullbackCross (roundMetric (E := F) (n := n)) (sphereLinearDiffeo (n := n) e)
    (f := (f : sphere (0 : F) 1 → ℝ))
    (f.contMDiff.contMDiffAt.of_le (by decide)) (x := x)
  rw [sphereLinearDiffeo_pullback_round] at hnat
  have hl := laplacian_levi_eq (roundMetric (E := E) (n := n))
    (f.contMDiff.comp (sphereLinearDiffeo (n := n) e).contMDiff) x
  have hr := laplacian_levi_eq (roundMetric (E := F) (n := n))
    f.contMDiff (sphereLinearDiffeo (n := n) e x)
  exact hl.symm.trans (hnat.trans hr)

end DFLSphereIsometric
