import continuation.CotSphereMetric
import continuation.ProductGradientSlices
import DifferentialGeometry.Geometry.Operator.GradientPullback

/-! The original angular/latitude Dirichlet density, for the actual
round-sphere gradient and the actual cot sphere map. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)]

/-- The original sphere map has a genuinely surjective differential at
every point of the angular-sphere-times-line domain. -/
theorem cotSpherePD_mfderiv_surjective (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    Function.Surjective
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q) := by
  have hD := ((cotSphereDiffeo (n := n) p).mfderivToContinuousLinearEquiv
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) q).surjective
  intro v
  obtain ⟨w, hw⟩ := hD v
  refine ⟨w, ?_⟩
  rw [← cotSphereDiffeo_mfderiv]
  exact hw

/-- Pullback of an actual smooth sphere observable along the proved cot
map, as an actual smooth function on the whole product manifold. -/
def cotSpherePullback (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮(𝓡 n).prod 𝓘(ℝ, ℝ), PolarDir p × ℝ; ℝ⟯ :=
  ⟨u ∘ cotSpherePD (n := n) p, u.contMDiff.comp (cotSpherePD_smooth (n := n) p)⟩

/-- Actual sphere Dirichlet density equals actual pullback Dirichlet
density. No gradient transformation is assumed. -/
theorem cotSpherePD_normGradSq (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (q : PolarDir p × ℝ) :
    normGradSqFun (cotProductMetric (n := n) p) (cotSpherePullback p u) q =
      normGradSqFun (roundMetric (E := E) (n := n+1)) u (cotSpherePD (n := n) p q) := by
  exact normGradSqFun_eq_of_pullback_inner (cotProductMetric (n := n) p)
    (roundMetric (E := E) (n := n+1)) (cotSpherePD (n := n) p) q
    ((cotSpherePD_smooth (n := n) p).mdifferentiableAt (by simp))
    (cotProductMetric_inner_pullback p q) (cotSpherePD_mfderiv_surjective p q) u
    (u.contMDiff.mdifferentiableAt (by simp))

/-- The original angular-plus-latitude energy formula, proved for the
true sphere gradient and the actual angular slice gradients. -/
theorem cotSpherePD_gradient_energy (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (q : PolarDir p × ℝ) :
    normGradSqFun (roundMetric (E := E) (n := n+1)) u (cotSpherePD (n := n) p q) =
      (cotAngularScale q.2^2)⁻¹*
        normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
          (fun y : PolarDir p => u (cotSpherePD (n := n) p (y,q.2))) q.1+
      (cotLineScale q.2^2)⁻¹*
        (deriv (fun s : ℝ => u (cotSpherePD (n := n) p (q.1,s))) q.2)^2 := by
  rw [← cotSpherePD_normGradSq p u q]
  exact DFLProductSlices.separated_gradient_energy_slices
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    (cotProductMetric_separated p) (cotSpherePullback p u) q

end DFLCotSphere
