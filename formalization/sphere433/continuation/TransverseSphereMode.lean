import continuation.RoundSphereLatitudeOperator
import continuation.OriginalWeightedGround
import continuation.RoundSphereActualTiltProfile

/-! Realizing the original transverse latitude mode on the physical
unit round sphere. Every differential expression below uses the actual
round metric, Levi-Civita connection, gradient, and scalar Laplacian. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLSpectralCoordinates DFLLatitudeOperator DFL.Spectral DFLSphere
namespace DFLTransverseSphere
/-- A C² original weighted profile equation holds at both poles by
continuity; no extra boundary equation is assumed. -/
theorem latitudeEigenEquation_closed (M : ℕ) (b lam0 r lam : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heig : LatitudeEigenEquation M b lam0 r lam v) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      -(1-t^2)*deriv (deriv v) t+((M : ℝ)*t-r*(1-t^2))*deriv v t+
        (lam0+b*r*t)*v t = lam*v t := by
  let f := fun t : ℝ => -(1-t^2)*deriv (deriv v) t+
    ((M : ℝ)*t-r*(1-t^2))*deriv v t+(lam0+b*r*t)*v t
  have hc0 := hv.continuous
  have hc1 : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  have hc2 : Continuous (deriv (deriv v)) :=
    ((hv.deriv' : ContDiff ℝ 1 (deriv v)).deriv' : ContDiff ℝ 0 (deriv (deriv v))).continuous
  have hcf : Continuous f := by dsimp [f]; fun_prop
  have hclosed : IsClosed {t : ℝ | f t = lam*v t} :=
    isClosed_eq hcf (continuous_const.mul hc0)
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {t : ℝ | f t = lam*v t} := by
    intro t ht
    exact heig t ht
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcl
  intro t ht
  exact hcl ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)]

omit [FiniteDimensional ℝ E] in
/-- The cross-coordinate gradient identity follows from the actual ambient
representatives of the two round gradients. -/
theorem coordinate_gradient_inner (p a : E) (x : sphere (0 : E) 1) :
    (roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) a) x) =
      ⟪p,a⟫_ℝ -⟪p,(x : E)⟫_ℝ *⟪a,(x : E)⟫_ℝ := by
  rw [roundMetric_inner]
  change ⟪dIncl (n := n) x (gradFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x),
    dIncl (n := n) x (gradFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) a) x)⟫_ℝ = _
  rw [dIncl_coordinate_gradient,dIncl_coordinate_gradient]
  have hxx : ⟪(x : E),(x : E)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,norm_eq_of_mem_sphere x]
    norm_num
  have hxa : ⟪(x : E),a⟫_ℝ = ⟪a,(x : E)⟫_ℝ := real_inner_comm _ _
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hxx,hxa]
  ring

variable [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- The genuine product Laplacian is exactly the original first transverse
latitude expression, including its dimensional shift by two. -/
theorem transverse_laplacian (p a : E) (hp : ‖p‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (x : sphere (0 : E) 1) :
    laplacian (LeviCivita (roundMetric (E := E) (n := n))) (roundMetric (E := E) (n := n))
      (fun y : sphere (0 : E) 1 => ⟪a,(y : E)⟫_ℝ *v ⟪p,(y : E)⟫_ℝ) x =
    ⟪a,(x : E)⟫_ℝ *((1-⟪p,(x : E)⟫_ℝ ^2)*deriv (deriv v) ⟪p,(x : E)⟫_ℝ -
      ((n+2 : ℕ) : ℝ)*⟪p,(x : E)⟫_ℝ *deriv v ⟪p,(x : E)⟫_ℝ -(n : ℝ)*v ⟪p,(x : E)⟫_ℝ) := by
  let g := roundMetric (E := E) (n := n)
  let z := innerCoordFun (n := n) a
  let t := innerCoordFun (n := n) p
  let h := fun y : sphere (0 : E) 1 => v (t y)
  have hzC : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 z := z.contMDiff.of_le (by decide)
  have htC : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 t := t.contMDiff.of_le (by decide)
  have hhC : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 h := hv.contMDiff.comp htC
  have hzD := hzC.mdifferentiable (by norm_num)
  have hhD := hhC.mdifferentiable (by norm_num)
  have hgZ := (gradientFun_contMDiffAt_one g (x₀ := x) hzC.contMDiffAt).mdifferentiableAt (by norm_num)
  have hgH := (gradientFun_contMDiffAt_one g (x₀ := x) hhC.contMDiffAt).mdifferentiableAt (by norm_num)
  have hmul := laplacian_mul_at (LeviCivita g) g
    (Eventually.of_forall hzD) (Eventually.of_forall hhD) hgZ hgH
  have hlZ : laplacian (LeviCivita g) g z x = -(n : ℝ)*z x := by
    calc
      _ = ΔG g z x := laplacian_levi_eq g z.contMDiff x
      _ = _ := coordinate_laplacian x a
  have hlH := latitude_laplacian (n := n) p hp v hv x
  change laplacian (LeviCivita g) g h x = (1-(t x)^2)*deriv (deriv v) (t x)-
    (n : ℝ)*t x*deriv v (t x) at hlH
  have hcross : g.inner x (gradientFun g z x) (gradientFun g h x) =
      -(z x*t x)*deriv v (t x) := by
    have hchain := gradientFun_comp g (hv.differentiable (by norm_num) (t x)) (t.contMDiff.mdifferentiable (by simp) x)
    change gradientFun g h x = deriv v (t x) • gradientFun g t x at hchain
    rw [hchain]
    simp only [map_smul,smul_eq_mul]
    have hc := coordinate_gradient_inner (n := n) a p x
    change g.inner x (gradientFun g z x) (gradientFun g t x) = ⟪a,p⟫_ℝ -z x*t x at hc
    rw [hc,hpa]
    ring
  change laplacian (LeviCivita g) g (fun y => z y*h y) x = _
  rw [hmul,hlZ]
  rw [hlH,hcross]
  change ⟪a,(x : E)⟫_ℝ *((1-⟪p,(x : E)⟫_ℝ ^2)*deriv (deriv v) ⟪p,(x : E)⟫_ℝ -
      (n : ℝ)*⟪p,(x : E)⟫_ℝ *deriv v ⟪p,(x : E)⟫_ℝ)+
    v ⟪p,(x : E)⟫_ℝ *(-(n : ℝ)*⟪a,(x : E)⟫_ℝ)+
    2*(-(⟪a,(x : E)⟫_ℝ *⟪p,(x : E)⟫_ℝ)*deriv v ⟪p,(x : E)⟫_ℝ) = _
  push_cast
  ring

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The actual drift contraction of the transverse mode. -/
theorem transverse_drift (p a : E) (hp : ‖p‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (x : sphere (0 : E) 1) :
    (roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)
      (gradientFun (roundMetric (E := E) (n := n))
        (fun y : sphere (0 : E) 1 => ⟪a,(y : E)⟫_ℝ *v ⟪p,(y : E)⟫_ℝ) x) =
      ⟪a,(x : E)⟫_ℝ *((1-⟪p,(x : E)⟫_ℝ ^2)*deriv v ⟪p,(x : E)⟫_ℝ -
        ⟪p,(x : E)⟫_ℝ *v ⟪p,(x : E)⟫_ℝ) := by
  let g := roundMetric (E := E) (n := n)
  let z := innerCoordFun (n := n) a
  let t := innerCoordFun (n := n) p
  let h := fun y : sphere (0 : E) 1 => v (t y)
  have hzD := z.contMDiff.mdifferentiable (by simp)
  have htD := t.contMDiff.mdifferentiable (by simp)
  have hhD : MDifferentiable (𝓡 n) 𝓘(ℝ,ℝ) h :=
    (hv.differentiable (by norm_num)).mdifferentiable.comp htD
  have hm := gradientFun_mul g (hzD x) (hhD x)
  have hc := gradientFun_comp g (hv.differentiable (by norm_num) (t x)) (htD x)
  change gradientFun g (fun y => z y*h y) x = z x • gradientFun g h x+h x • gradientFun g z x at hm
  change gradientFun g h x = deriv v (t x) • gradientFun g t x at hc
  change g.inner x (gradientFun g t x) (gradientFun g (fun y => z y*h y) x) = _
  rw [hm,hc]
  simp only [map_add,map_smul,smul_eq_mul]
  have hnorm := latitude_gradient_norm_sq (n := n) p hp x
  have hpair := coordinate_gradient_inner (n := n) p a x
  have hap : ⟪p,a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpa
  rw [hnorm,hpair,hap]
  change ⟪a,(x : E)⟫_ℝ *(deriv v ⟪p,(x : E)⟫_ℝ *(1-⟪p,(x : E)⟫_ℝ ^2))+
    v ⟪p,(x : E)⟫_ℝ *(0-⟪p,(x : E)⟫_ℝ *⟪a,(x : E)⟫_ℝ) = _
  ring

/-- The actual original transverse physical function. -/
def transverseMode (p a : E) (v : ℝ → ℝ) (x : sphere (0 : E) 1) : ℝ :=
  ⟪a,(x : E)⟫_ℝ *v ⟪p,(x : E)⟫_ℝ

/-- The actual weighted round differential expression for density exp(rt). -/
def weightedRoundApply (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ)
    (x : sphere (0 : E) 1) : ℝ :=
  -laplacian (LeviCivita (roundMetric (E := E) (n := n))) (roundMetric (E := E) (n := n)) f x-
    r*(roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)
      (gradientFun (roundMetric (E := E) (n := n)) f x)

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- A genuine C² manifold representative is obtained by ordinary composition
and multiplication of the two real coordinate functions. -/
theorem transverseMode_contMDiff (p a : E) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (transverseMode p a v) := by
  have hp : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (innerCoordFun (n := n) p) :=
    (innerCoordFun (n := n) p).contMDiff.of_le (by decide)
  have ha : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (innerCoordFun (n := n) a) :=
    (innerCoordFun (n := n) a).contMDiff.of_le (by decide)
  exact ha.mul (hv.contMDiff.comp hp)

omit [FiniteDimensional ℝ E] in
/-- An original weighted eigenprofile yields a real physical-sphere
weighted eigenfunction, at every point including both poles. -/
theorem transverseMode_weighted_eigen (p a : E) (hp : ‖p‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0)
    (r lam : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heig : LatitudeEigenEquation (n+2) 1 (n : ℝ) r lam v) :
    ∀ x : sphere (0 : E) 1,
      weightedRoundApply (n := n) p r (transverseMode p a v) x = lam*transverseMode p a v x := by
  intro x
  have hb := abs_real_inner_le_norm p (x : E)
  rw [hp,norm_eq_of_mem_sphere x,mul_one] at hb
  have htx : ⟪p,(x : E)⟫_ℝ ∈ Icc (-1 : ℝ) 1 := abs_le.mp hb
  have he := latitudeEigenEquation_closed (n+2) 1 (n : ℝ) r lam v hv heig _ htx
  have he' := congrArg (fun q : ℝ => ⟪a,(x : E)⟫_ℝ *q) he
  unfold weightedRoundApply transverseMode
  rw [transverse_laplacian p a hp hpa v hv x,transverse_drift p a hp hpa v hv x]
  linear_combination he'

omit [FiniteDimensional ℝ E] [NeZero n] [Fact (finrank ℝ E = n+1)] in
/-- A unit transverse axis is a point where the physical mode is positive;
the mode is therefore a genuine nonzero state. -/
theorem transverseMode_nonzero (p a : E) (ha : ‖a‖ = 1) (hpa : ⟪a,p⟫_ℝ = 0)
    (v : ℝ → ℝ) (hv0 : 0 < v 0) : transverseMode p a v ≠ 0 := by
  intro hz
  let x : sphere (0 : E) 1 := ⟨a,by rw [mem_sphere_zero_iff_norm]; exact ha⟩
  have he := congrArg (fun f : sphere (0 : E) 1 → ℝ => f x) hz
  have hap : ⟪p,a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpa
  change ⟪a,a⟫_ℝ *v ⟪p,a⟫_ℝ = 0 at he
  rw [real_inner_self_eq_norm_sq,ha,hap] at he
  norm_num at he
  exact hv0.ne' he

omit [FiniteDimensional ℝ E] in
/-- The actual auxiliary minimum has a nonzero transverse realization on
the original physical Sⁿ, without any assumed mode or spectral bridge. -/
theorem actual_transverse_ground_exists (p a : E) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1)
    (hpa : ⟪a,p⟫_ℝ = 0) (r : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm (n+2) r v = 1 ∧
      ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (transverseMode p a v) ∧ transverseMode p a v ≠ 0 ∧
      ∀ x : sphere (0 : E) 1, weightedRoundApply (n := n) p r (transverseMode p a v) x =
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*transverseMode p a v x := by
  obtain ⟨v,hv,hpos,hn,heig⟩ := original_weighted_positive_ground_exists (n+2) (by omega) 1 (n : ℝ) r
  have hn2 : n+2-2 = n := by omega
  have he : ((n+2 : ℕ) : ℝ)/2-1 = (n : ℝ)/2 := by push_cast; ring
  rw [hn2,he] at heig
  refine ⟨v,hv,hpos,hn,transverseMode_contMDiff p a v hv,
    transverseMode_nonzero p a ha hpa v (hpos 0 (by norm_num)),?_⟩
  exact transverseMode_weighted_eigen p a hp hpa r _ v hv heig

end DFLTransverseSphere
