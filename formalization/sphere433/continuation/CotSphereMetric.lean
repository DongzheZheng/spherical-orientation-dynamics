import continuation.CotSphereDifferential
import continuation.PolarRoundMetric
import continuation.WarpedProductVolume

/-! The actual round metric pulled back along the same global cot sphere
diffeomorphism. Its separated coefficients are derived by the actual
chain rule and the actual polar differential, without a supplied metric
or Jacobian identity. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)]

/-- True tangent chain rule for the globally regular cot parametrization. -/
theorem cotSpherePD_mfderiv (p : sphere (0 : E) 1) (q : PolarDir p × ℝ)
    (v : TangentSpace (𝓡 n) q.1 × ℝ) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q v =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n+1)) (spherePolarPD (n := n) p)
        (cotAngle q.2,q.1) (-cotLineScale q.2*v.2,v.1) := by
  have hC : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (cotPolarParameterPD (n := n) p) :=
    contMDiffOn_univ.mp (cotPolarParameterPD (n := n) p).contMDiffOn_toFun
  have hCd := hC.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := q)
  have hP := (DFLPolarRound.spherePolarPD_smooth (n := n) p).mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := cotPolarParameterPD (n := n) p q)
  have hc := mfderiv_comp_apply q hP hCd v
  change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) (cotSpherePD (n := n) p) q v = _ at hc
  rw [cotPolarParameterPD_mfderiv] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- The actual global pullback of the true round metric is precisely the
original angular/longitudinal separated metric in cot coordinates. -/
theorem cotProductMetric_inner (p : sphere (0 : E) 1) (q : PolarDir p × ℝ)
    (v w : TangentSpace (𝓡 n) q.1 × ℝ) :
    (cotProductMetric (n := n) p).inner q v w =
      cotAngularScale q.2^2 *
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)).inner q.1 v.1 w.1 +
      cotLineScale q.2^2*v.2*w.2 := by
  rw [cotProductMetric_inner_pullback,cotSpherePD_mfderiv,cotSpherePD_mfderiv]
  change (roundMetric (E := E) (n := n+1)).inner
      (spherePolarPD (n := n) p (cotAngle q.2,q.1))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n+1)) (spherePolarPD (n := n) p)
        (cotAngle q.2,q.1) (-cotLineScale q.2*v.2,v.1))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n+1)) (spherePolarPD (n := n) p)
        (cotAngle q.2,q.1) (-cotLineScale q.2*w.2,w.1)) = _
  rw [DFLPolarRound.spherePolarPD_round_inner]
  dsimp only
  rw [cotAngle_sin]
  ring

/-- The manuscript's separated metric formula, on the whole product. -/
theorem cotProductMetric_separated (p : sphere (0 : E) 1)
    (y : PolarDir p) (s : ℝ) (v w : TangentSpace (𝓡 n) y) (a c : ℝ) :
    (cotProductMetric (n := n) p).inner (y,s) (v,a) (w,c) =
      cotAngularScale s^2 *
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)).inner y v w +
      cotLineScale s^2*a*c := cotProductMetric_inner p (y,s) (v,a) (w,c)

/-- The actual physical axial coordinate in the same cot parametrization. -/
theorem cotSpherePD_height (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    ⟪(p : E),(cotSpherePD (n := n) p q : E)⟫_ℝ = q.2*cotAngularScale q.2 := by
  have hpp : ⟪(p : E),(p : E)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,norm_eq_of_mem_sphere p]
    norm_num
  have hpy : ⟪(p : E),((q.1 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.1.1.2
  rw [cotSpherePD_ambient,real_inner_smul_right,inner_add_right,
    real_inner_smul_right,hpp,hpy]
  ring

end DFLCotSphere
