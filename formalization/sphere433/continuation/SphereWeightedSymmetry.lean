import continuation.RoundSphereGroundSymmetry
import continuation.TransverseSphereMode
import DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt

/-! Actual round weighted operators commute with genuine orthogonal
sphere symmetries fixing their field axis. The drift is transported by
actual differential, pullback metric, and gradient naturality. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLTransverseSphere DFLGroundSymmetry
namespace DFLWeightedSymmetry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]

omit [NeZero n] in
/-- True orthogonal pullback of the round-gradient inner product. -/
theorem orthogonalPullback_gradient_inner (e : E ≃ₗᵢ[ℝ] E)
    (f h : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    (roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) (orthogonalPullback e f) x)
      (gradientFun (roundMetric (E := E) (n := n)) (orthogonalPullback e h) x) =
    (roundMetric (E := E) (n := n)).inner (sphereDiffeo (n := n) e x)
      (gradientFun (roundMetric (E := E) (n := n)) f (sphereDiffeo (n := n) e x))
      (gradientFun (roundMetric (E := E) (n := n)) h (sphereDiffeo (n := n) e x)) := by
  let g := roundMetric (E := E) (n := n)
  let Φ := sphereDiffeo (n := n) e
  have hmetric : Diffeomorph.pullbackMetricCross g Φ = g := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact pullbackMetric_round_eq e
  have hinner : ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = g.inner (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v)
        (mfderiv (𝓡 n) (𝓡 n) Φ x w) := by
    intro v w
    calc
      _ = (Diffeomorph.pullbackMetricCross g Φ).inner x v w :=
        congrArg (fun G => G.inner x v w) hmetric.symm
      _ = _ := Diffeomorph.pullbackMetricCross_inner g Φ x v w
  have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) Φ x) := by
    have hh := (Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : ℕ∞ω) ≠ 0) x).surjective
    have he : (Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : ℕ∞ω) ≠ 0) x :
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) (Φ x)) =
        mfderiv (𝓡 n) (𝓡 n) Φ x := Φ.mfderivToContinuousLinearEquiv_coe _
    intro v
    obtain ⟨w,hw⟩ := hh v
    refine ⟨w,?_⟩
    exact (congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) (Φ x) => L w) he).symm.trans hw
  have hΦ := Φ.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0) (x := x)
  have hgf := mfderiv_gradientFun_comp_of_pullback_inner g g hΦ hinner hsurj
    (f.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0) (x := Φ x))
  have hgh := mfderiv_gradientFun_comp_of_pullback_inner g g hΦ hinner hsurj
    (h.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0) (x := Φ x))
  change g.inner x (gradientFun g (f ∘ Φ) x) (gradientFun g (h ∘ Φ) x) = _
  rw [hinner,hgf,hgh]

omit [NeZero n] in
/-- The original actual weighted round operator has the true symmetry;
its pointwise commutation is derived from geometry. -/
theorem orthogonalPullback_weightedRoundApply (p : E) (r : ℝ)
    (e : E ≃ₗᵢ[ℝ] E) (hep : e p = p)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    weightedRoundApply (n := n) p r (orthogonalPullback e u) x =
      weightedRoundApply (n := n) p r u (sphereDiffeo (n := n) e x) := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  have htf : (orthogonalPullback e t : sphere (0 : E) 1 → ℝ) = t := by
    funext y
    exact axis_potential_invariant p id e hep y
  have hgrad := orthogonalPullback_gradient_inner e t u x
  rw [htf] at hgrad
  have hl := orthogonalPullback_laplacian e u x
  have hleft := laplacian_levi_eq g (orthogonalPullback e u).contMDiff x
  have hright := laplacian_levi_eq g u.contMDiff (sphereDiffeo (n := n) e x)
  have hLap : laplacian (LeviCivita g) g (orthogonalPullback e u) x =
      laplacian (LeviCivita g) g u (sphereDiffeo (n := n) e x) :=
    hleft.trans (hl.trans hright.symm)
  unfold weightedRoundApply
  rw [hLap,hgrad]

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The actual smooth weighted expression is linear, derived from its
true Laplacian and true gradient rather than supplied as an operator axiom. -/
theorem weightedRoundApply_linear (p : E) (r a b : ℝ)
    (f h : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    weightedRoundApply (n := n) p r (fun y => a*f y+b*h y) x =
      a*weightedRoundApply (n := n) p r f x+b*weightedRoundApply (n := n) p r h x := by
  let g := roundMetric (E := E) (n := n)
  let af : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ := ⟨fun y => a*f y,contMDiff_const.mul f.contMDiff⟩
  let bh : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ := ⟨fun y => b*h y,contMDiff_const.mul h.contMDiff⟩
  have hfa := af.contMDiff.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hhb := bh.contMDiff.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hff := f.contMDiff.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hhh := h.contMDiff.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hGa := (gradientFun_contMDiffAt_one g (af.contMDiff.contMDiffAt.of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞))).mdifferentiableAt (by norm_num) (x := x)
  have hGb := (gradientFun_contMDiffAt_one g (bh.contMDiff.contMDiffAt.of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞))).mdifferentiableAt (by norm_num) (x := x)
  have hGf := (gradientFun_contMDiffAt_one g (f.contMDiff.contMDiffAt.of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞))).mdifferentiableAt (by norm_num) (x := x)
  have hGh := (gradientFun_contMDiffAt_one g (h.contMDiff.contMDiffAt.of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞))).mdifferentiableAt (by norm_num) (x := x)
  have hL := laplacian_add_at (LeviCivita g) g (Eventually.of_forall hfa) (Eventually.of_forall hhb) hGa hGb
  have hLa := laplacian_smul_at (LeviCivita g) g a (Eventually.of_forall hff) hGf
  have hLb := laplacian_smul_at (LeviCivita g) g b (Eventually.of_forall hhh) hGh
  have hGr := gradientFun_add g (hfa x) (hhb x)
  have hGra := gradientFun_const_smul g a (hff x)
  have hGrb := gradientFun_const_smul g b (hhh x)
  change laplacian (LeviCivita g) g af x = _ at hLa
  change laplacian (LeviCivita g) g bh x = _ at hLb
  change gradientFun g af x = _ at hGra
  change gradientFun g bh x = _ at hGrb
  unfold weightedRoundApply
  change -laplacian (LeviCivita g) g (fun y => af y+bh y) x-
    r*g.inner x (gradientFun g (innerCoordFun (n := n) p) x)
      (gradientFun g (fun y => af y+bh y) x) = _
  rw [hL,hLa,hLb,hGr,hGra,hGrb]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

end DFLWeightedSymmetry
