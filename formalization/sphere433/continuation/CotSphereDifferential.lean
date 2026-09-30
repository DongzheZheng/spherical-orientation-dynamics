import continuation.CotSphereDiffeomorph
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

/-! Actual differential and actual global pullback metric for the same
cot-parameter sphere diffeomorphism. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)]

theorem cotAngle_hasDerivAt (s : ℝ) : HasDerivAt cotAngle (-cotLineScale s) s := by
  with_unfolding_all
    simpa only [cotAngle,cotLineScale,zero_sub] using!
      (hasDerivAt_const s (Real.pi/2)).sub (Real.hasDerivAt_arctan' s)

/-- True derivative of the actual source reparametrization. -/
theorem cotPolarParameterPD_mfderiv (p : sphere (0 : E) 1) (q : PolarDir p × ℝ)
    (v : TangentSpace (𝓡 n) q.1 × ℝ) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 n))
      (cotPolarParameterPD (n := n) p) q v = (-cotLineScale q.2*v.2,v.1) := by
  have hS : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd q :=
    contMDiff_snd.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hA : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) cotAngle q.2 :=
    cotAngle_smooth.contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hF : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n) Prod.fst q :=
    contMDiff_fst.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have htheta : mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun x : PolarDir p × ℝ => cotAngle x.2) q v = -cotLineScale q.2*v.2 := by
    have hc := hA.mvfderiv_comp_apply hS v
    rw [mfderiv_snd] at hc
    change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun x : PolarDir p × ℝ => cotAngle x.2) q v =
        mvfderiv 𝓘(ℝ, ℝ) cotAngle q.2 v.2 at hc
    have hL : mvfderiv 𝓘(ℝ, ℝ) cotAngle q.2 =
        (1 : ℝ →L[ℝ] ℝ).smulRight (-cotLineScale q.2) := by
      simp only [mvfderiv,mfderiv_eq_fderiv,
        (cotAngle_hasDerivAt q.2).hasFDerivAt.fderiv]
      with_unfolding_all rfl
    rw [hc,hL]
    change v.2 * -cotLineScale q.2 = _
    ring
  have hthetaD : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun x : PolarDir p × ℝ => cotAngle x.2) q := hA.comp q hS
  change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 n))
    (fun x : PolarDir p × ℝ => (cotAngle x.2,x.1)) q v = _
  rw [mfderiv_prodMk hthetaD hF]
  change (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
    (fun x : PolarDir p × ℝ => cotAngle x.2) q v,
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n) Prod.fst q v) = _
  rw [htheta,mfderiv_fst]
  rfl

/-- The genuine target-open-submanifold diffeomorphism has exactly the
same differential as the original partial sphere map. -/
theorem cotSphereDiffeo_mfderiv (p : sphere (0 : E) 1) (q : PolarDir p × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSphereDiffeo (n := n) p) q v =
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q v := by
  have hD := (cotSphereDiffeo (n := n) p).contMDiff.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := q)
  have hval := (contMDiff_subtype_val (I := 𝓡 (n+1)) (U := cotSphereTarget (n := n) p)).mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := cotSphereDiffeo (n := n) p q)
  have hc := mfderiv_comp_apply q hval hD v
  rw [mfderiv_subtype_val_apply] at hc
  exact hc.symm

/-- The actual pullback of the true restricted round metric by the actual
global cot diffeomorphism, defined on the whole angular sphere times ℝ. -/
def cotProductMetric (p : sphere (0 : E) 1) :
    SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ) :=
  Diffeomorph.pullbackMetricCross
    ((roundMetric (E := E) (n := n+1)).restrictOpen (cotSphereTarget (n := n) p))
    (cotSphereDiffeo (n := n) p)

theorem cotProductMetric_inner_pullback (p : sphere (0 : E) 1) (q : PolarDir p × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q) :
    (cotProductMetric (n := n) p).inner q v w =
      (roundMetric (E := E) (n := n+1)).inner (cotSpherePD (n := n) p q)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q w) := by
  rw [cotProductMetric,Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner,cotSphereDiffeo_coe,
    cotSphereDiffeo_mfderiv,cotSphereDiffeo_mfderiv]

end DFLCotSphere
