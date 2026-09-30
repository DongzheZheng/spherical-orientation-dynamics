import continuation.TransverseSphereMode

/-! The manuscript's half-density change on the actual physical sphere.
Its operator identity follows from the true scalar product and chain rules. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLSpectralCoordinates DFLLatitudeOperator DFLTransverseSphere
namespace DFLPhysicalHalfDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n+1)]

/-- Positive multiplication in the original half-density transform. -/
def halfFactor (p : E) (r : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  Real.exp (r*⟪p,(x : E)⟫_ℝ/2)

omit [FiniteDimensional ℝ E] in
theorem halfFactor_smooth (p : E) (r : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (halfFactor p r) := by
  exact Real.contDiff_exp.contMDiff.comp
    (contMDiff_const.mul (innerCoordFun (n := n) p).contMDiff |>.div_const 2)

/-- The real half-density Schrödinger potential on S^n. -/
def physicalPotential (p : E) (r : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  r^2/4*(1-⟪p,(x : E)⟫_ℝ ^2)-(n : ℝ)*r/2*⟪p,(x : E)⟫_ℝ

variable [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- Exact conjugacy of the actual round operators; all derivatives are
the genuine Levi-Civita derivatives of the functions on the sphere. -/
theorem weighted_half_density_conjugacy (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    -laplacian (LeviCivita (roundMetric (E := E) (n := n)))
        (roundMetric (E := E) (n := n)) (fun y => halfFactor p r y*u y) x+
      physicalPotential (n := n) p r x*(halfFactor p r x*u x) =
      halfFactor p r x*weightedRoundApply (n := n) p r u x := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  let v := fun z : ℝ => Real.exp (r*z/2)
  let h := halfFactor p r
  have hv : ContDiff ℝ 2 v := by dsimp [v]; fun_prop
  have hv1 (z : ℝ) : HasDerivAt v (r/2*v z) z := by
    have hid : v = fun y : ℝ => Real.exp (r/2*y) := by
      funext y
      apply congrArg Real.exp
      ring
    rw [hid]
    simpa only [id_eq,mul_comm,one_mul] using ((hasDerivAt_id z).const_mul (r/2)).exp
  have hv2 (z : ℝ) : HasDerivAt (deriv v) ((r/2)^2*v z) z := by
    have hid : deriv v = fun z => r/2*v z := funext (fun z => (hv1 z).deriv)
    rw [hid]
    convert! (hv1 z).const_mul (r/2) using 1; first | rfl | ring
  have hLap := latitude_laplacian (n := n) p hp v hv x
  change laplacian (LeviCivita g) g h x = _ at hLap
  rw [(hv1 _).deriv,(hv2 _).deriv] at hLap
  have hC := halfFactor_smooth (n := n) p r
  have hgradH := (gradientFun_contMDiffAt_one g (x₀ := x)
    (hC.contMDiffAt.of_le (by decide))).mdifferentiableAt (by norm_num)
  have hgradU := (gradientFun_contMDiffAt_one g (x₀ := x)
    (u.contMDiff.contMDiffAt.of_le (by decide))).mdifferentiableAt (by norm_num)
  have hmul := laplacian_mul_at (LeviCivita g) g
    (Eventually.of_forall (hC.mdifferentiable (by simp)))
    (Eventually.of_forall (u.contMDiff.mdifferentiable (by simp))) hgradH hgradU
  have hchain := gradientFun_comp g (hv.differentiable (by norm_num) (t x))
    (t.contMDiff.mdifferentiable (by simp) x)
  change gradientFun g h x = deriv v (t x) • gradientFun g t x at hchain
  rw [(hv1 _).deriv] at hchain
  have hcross : g.inner x (gradientFun g h x) (gradientFun g u x) =
      (r/2*h x)*g.inner x (gradientFun g t x) (gradientFun g u x) := by
    rw [hchain]
    simp only [map_smul]
    rfl
  change -laplacian (LeviCivita g) g (fun y => h y*u y) x+
    physicalPotential (n := n) p r x*(h x*u x) = h x*weightedRoundApply (n := n) p r u x
  rw [hmul,hcross,hLap]
  unfold physicalPotential weightedRoundApply
  change -(h x*laplacian (LeviCivita g) g u x+
    u x*((1-(t x)^2)*((r/2)^2*h x)-(n : ℝ)*t x*(r/2*h x))+
    2*((r/2*h x)*g.inner x (gradientFun g t x) (gradientFun g u x)))+
    (r^2/4*(1-(t x)^2)-(n : ℝ)*r/2*t x)*(h x*u x) =
    h x*(-laplacian (LeviCivita g) g u x-r*g.inner x (gradientFun g t x) (gradientFun g u x))
  ring


omit [FiniteDimensional ℝ E] [NeZero n] in
/-- Positive and negative half-density factors are genuine inverses. -/
theorem halfFactor_cancel (p : E) (r : ℝ) (x : sphere (0 : E) 1) :
    halfFactor p r x*halfFactor p (-r) x = 1 := by
  unfold halfFactor
  rw [← Real.exp_add]
  have hz : r*⟪p,(x : E)⟫_ℝ/2+(-r)*⟪p,(x : E)⟫_ℝ/2 = 0 := by ring
  rw [hz,Real.exp_zero]

/-- The original physical observable obtained by inverse half density. -/
def inverseHalfDensity (p : E) (r : ℝ)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ :=
  ⟨fun x => halfFactor p (-r) x*u x,(halfFactor_smooth (n := n) p (-r)).mul u.contMDiff⟩

omit [FiniteDimensional ℝ E] in
/-- A true classical Schrödinger eigenstate is a true eigenstate of the
original density-weighted sphere generator after inverse half density. -/
theorem schrodinger_to_weighted_eigenfunction (p : E) (hp : ‖p‖ = 1) (r lam : ℝ)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hu : ∀ x, -ΔG (roundMetric (E := E) (n := n)) u x+
      physicalPotential (n := n) p r x*u x = lam*u x) :
    ∀ x, weightedRoundApply (n := n) p r (inverseHalfDensity (n := n) p r u) x =
      lam*inverseHalfDensity (n := n) p r u x := by
  intro x
  let g := roundMetric (E := E) (n := n)
  let f := inverseHalfDensity (n := n) p r u
  have hf (y : sphere (0 : E) 1) : halfFactor p r y*f y = u y := by
    change halfFactor p r y*(halfFactor p (-r) y*u y) = u y
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  have hfun : (fun y => halfFactor p r y*f y) = (u : sphere (0 : E) 1 → ℝ) := funext hf
  have hc := weighted_half_density_conjugacy p hp r f x
  rw [hfun,hf x] at hc
  have hlap : laplacian (LeviCivita g) g (u : sphere (0 : E) 1 → ℝ) x = ΔG g u x :=
    laplacian_levi_eq g u.contMDiff x
  have hux : -ΔG g u x+physicalPotential (n := n) p r x*u x = lam*u x := hu x
  rw [hlap,hux] at hc
  have heq : halfFactor p r x*weightedRoundApply (n := n) p r f x =
      halfFactor p r x*(lam*f x) := by
    rw [← hc,← hf x]
    ring
  exact mul_left_cancel₀ (Real.exp_pos _).ne' heq

end DFLPhysicalHalfDensity
