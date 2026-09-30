import continuation.PhysicalHalfDensity
import continuation.CompactC2WeakH1
import continuation.CompactPotentialGround

/-! The original half-density Dirichlet identity on the genuine physical
sphere. The cross term is integrated against the smooth weighted height
gradient; the observable itself only needs C² regularity. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DFLSpectralCoordinates DFLLatitudeOperator DFLC2WeakH1 DFLCompactPotential
namespace DFLPhysicalHalfDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero n] in
private theorem gradient_pair_continuous (p : E) (f : sphere (0 : E) 1 → ℝ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f) :
    Continuous (fun x => (roundMetric (E := E) (n := n)).inner x
      (gradientFun (roundMetric (E := E) (n := n)) f x)
      (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)) := by
  let g := roundMetric (E := E) (n := n)
  have hG : ContMDiff (𝓡 n) (𝓡 n).tangent 1
      (fun x => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (gradientFun g f x)) := by
    intro x
    exact gradientFun_contMDiffAt_one g hf.contMDiffAt
  have ht : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (innerCoordFun (n := n) p) :=
    (innerCoordFun (n := n) p).contMDiff.of_le (by decide)
  have hT : ContMDiff (𝓡 n) (𝓡 n).tangent 1
      (fun x => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (gradientFun g (innerCoordFun (n := n) p) x)) := by
    intro x
    exact gradientFun_contMDiffAt_one g ht.contMDiffAt
  let cg : Bundle.ContinuousRiemannianMetric (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _) := g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := Continuous.inner_bundle (F := EuclideanSpace ℝ (Fin n))
    (B := sphere (0 : E) 1) (E := (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _))
    (b := fun x => x) (v := gradientFun g f) (w := gradientFun g (innerCoordFun (n := n) p))
    hG.continuous hT.continuous
  exact h.congr (fun x => rfl)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n+1)] [NeZero n] in
/-- The actual half-density factor has exactly the original physical weight. -/
theorem halfFactor_square (p : E) (r : ℝ) (x : sphere (0 : E) 1) :
    (halfFactor p r x)^2 = Real.exp (r*⟪p,(x : E)⟫_ℝ) := by
  unfold halfFactor
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

/-- The original smooth weighted height flux supplies the exact cross-term
cancellation for every actual C² observable. -/
theorem half_density_cross_term (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f) :
    (∫ x, 2*Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x*
      (roundMetric (E := E) (n := n)).inner x
        (gradientFun (roundMetric (E := E) (n := n)) f x)
        (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) =
      -(∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*
        (r*(1-⟪p,(x : E)⟫_ℝ ^2)-(n : ℝ)*⟪p,(x : E)⟫_ℝ)*(f x)^2
        ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  let rho := fun x : sphere (0 : E) 1 => Real.exp (r*t x)
  have hR : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ rho :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul t.contMDiff)
  let X := smoothSmul rho hR (gradG g t)
  have hX (x : sphere (0 : E) 1) : X x = rho x • gradientFun g t x := by
    rw [smoothSmul_apply,grad_g_apply]
    rfl
  have hdiv (x : sphere (0 : E) 1) :
      divergenceG g X x = rho x*(r*(1-(t x)^2)-(n : ℝ)*t x) := by
    rw [divergence_g_smoothSmul]
    have hact : tangentSectionAction (gradG g t) rho x =
        r*rho x*(1-(t x)^2) := by
      have haction : tangentSectionAction (gradG g t) rho x =
          g.inner x (gradientFun g rho x) (gradientFun g t x) := by
        symm
        rw [inner_gradientFun,tangentSectionAction_def,mvfderiv_real_eq_mfderiv,grad_g_apply]
        rfl
      rw [haction]
      have hchain := gradientFun_comp g
        (((hasDerivAt_id (t x)).const_mul r).exp.differentiableAt)
        (t.contMDiff.mdifferentiable (by simp) x)
      have hder : deriv (fun z : ℝ => Real.exp (r*z)) (t x) = r*rho x := by
        have hd := ((hasDerivAt_id (t x)).const_mul r).exp
        simpa only [id_eq,one_mul,mul_one,rho,mul_comm] using hd.deriv
      change gradientFun g rho x = deriv (fun z : ℝ => Real.exp (r*z)) (t x) • gradientFun g t x at hchain
      rw [hchain,hder]
      simp only [map_smul,smul_apply,smul_eq_mul]
      rw [latitude_gradient_norm_sq p hp x]
      rfl
    rw [hact]
    change rho x*ΔG g t x+r*rho x*(1-(t x)^2) = _
    rw [coordinate_laplacian]
    change rho x*(-(n : ℝ)*t x)+r*rho x*(1-(t x)^2) = _
    ring
  have hw := contMDiff_one_hasWeakGrad g (fun x => f x*f x)
    ((hf.of_le (by decide : (1 : ℕ∞ω) ≤ 2)).mul (hf.of_le (by decide : (1 : ℕ∞ω) ≤ 2)))
  have hh := hw.pairing_eq X (HasCompactSupport.of_compactSpace _)
  have hleft : (fun x => g.inner x (gradientFun g (fun y => f y*f y) x) (X x)) =
      fun x => 2*rho x*f x*g.inner x (gradientFun g f x) (gradientFun g t x) := by
    funext x
    rw [gradientFun_mul_self g (hf.mdifferentiable (by norm_num) x),hX]
    simp only [map_smul,smul_apply]
    ring
  rw [hleft] at hh
  have hright : (fun x => (f x*f x)*divergenceG g X x) =
      fun x => rho x*(r*(1-(t x)^2)-(n : ℝ)*t x)*(f x)^2 := by
    funext x
    rw [hdiv]
    ring
  rw [hright] at hh
  exact hh


omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The actual gradient of the half-density multiplier. -/
theorem halfFactor_gradient (p : E) (r : ℝ) (x : sphere (0 : E) 1) :
    gradientFun (roundMetric (E := E) (n := n)) (halfFactor p r) x =
      (r/2*halfFactor p r x) •
        gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  let phi := fun z : ℝ => Real.exp (r*z/2)
  have hd (z : ℝ) : HasDerivAt phi (r/2*Real.exp (r*z/2)) z := by
    simpa only [phi,id_eq,mul_one,mul_comm] using
      (((hasDerivAt_id z).const_mul r).div_const 2).exp
  have hc := gradientFun_comp g (hd (t x)).differentiableAt
    (t.contMDiff.mdifferentiable (by simp) x)
  change gradientFun g (halfFactor p r) x = deriv phi (t x) • gradientFun g t x at hc
  rw [(hd _).deriv] at hc
  exact hc

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- Actual pointwise gradient energy of a half-density C² observable. -/
theorem half_density_gradient_square (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f)
    (x : sphere (0 : E) 1) :
    normGradSqFun (roundMetric (E := E) (n := n)) (fun y => halfFactor p r y*f y) x =
      Real.exp (r*⟪p,(x : E)⟫_ℝ)*
        (normGradSqFun (roundMetric (E := E) (n := n)) f x+
          r*f x*(roundMetric (E := E) (n := n)).inner x
            (gradientFun (roundMetric (E := E) (n := n)) f x)
            (gradientFun (roundMetric (E := E) (n := n)) (innerCoordFun (n := n) p) x)+
          r^2/4*(1-⟪p,(x : E)⟫_ℝ ^2)*(f x)^2) := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  let h := halfFactor p r
  have hG := gradientFun_mul g
    ((halfFactor_smooth (n := n) p r).mdifferentiable (by simp) x)
    (hf.mdifferentiable (by norm_num) x)
  change gradientFun g (fun y => h y*f y) x =
    h x • gradientFun g f x+f x • gradientFun g h x at hG
  rw [halfFactor_gradient] at hG
  change g.inner x (gradientFun g (fun y => h y*f y) x)
      (gradientFun g (fun y => h y*f y) x) = _
  rw [hG]
  simp only [map_add,add_apply,map_smul,smul_apply]
  have hsym : g.inner x (gradientFun g t x) (gradientFun g f x) =
      g.inner x (gradientFun g f x) (gradientFun g t x) := g.symm x _ _
  rw [hsym,latitude_gradient_norm_sq p hp x]
  calc
    _ = (h x)^2*(normGradSqFun g f x+
      r*f x*g.inner x (gradientFun g f x) (gradientFun g t x)+
      r^2/4*(1-⟪p,(x : E)⟫_ℝ ^2)*(f x)^2) := by
        unfold normGradSqFun
        change _ = (h x)^2*(g.inner x (gradientFun g f x) (gradientFun g f x)+_
          +r^2/4*(1-⟪p,(x : E)⟫_ℝ ^2)*(f x)^2)
        ring
    _ = _ := by rw [halfFactor_square]


/-- The half-density C² observable lies in the actual full H1 domain,
with the original weighted mass and weighted Dirichlet energy. -/
theorem half_density_exists_completion_mass_energy (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f) :
    ∃ U : H1Compl (roundMetric (E := E) (n := n)),
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          (fun x => halfFactor p r x*f x) ∧
      ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 =
        ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) ∧
      potentialEnergy (roundMetric (E := E) (n := n)) (physicalPotential (n := n) p r) U =
        ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n)) f x
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let _ : IsFiniteMeasure mu := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let h := halfFactor p r
  let t := innerCoordFun (n := n) p
  let rho := fun x : sphere (0 : E) 1 => Real.exp (r*t x)
  let C := fun x => 2*rho x*f x*g.inner x (gradientFun g f x) (gradientFun g t x)
  let D := fun x => rho x*(r*(1-(t x)^2)-(n : ℝ)*t x)*(f x)^2
  have hhf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 (fun x => h x*f x) :=
    ((halfFactor_smooth (n := n) p r).of_le (by decide)).mul hf
  obtain ⟨U,hU,hUE⟩ := contMDiff_two_exists_completion_energy g (fun x => h x*f x) hhf
  have hrhoc : Continuous rho :=
    Real.continuous_exp.comp (continuous_const.mul t.contMDiff.continuous)
  have hVc : Continuous (physicalPotential (n := n) p r) := by
    unfold physicalPotential
    fun_prop
  have hCc : Continuous C := by
    exact ((continuous_const.mul hrhoc).mul hf.continuous).mul
      (gradient_pair_continuous p f hf)
  have hDc : Continuous D :=
    (hrhoc.mul ((continuous_const.mul (continuous_const.sub (t.contMDiff.continuous.pow 2))).sub
      (continuous_const.mul t.contMDiff.continuous))).mul (hf.continuous.pow 2)
  have hGI : Integrable (fun x => rho x*normGradSqFun g f x) mu :=
    (hrhoc.mul (contMDiff_two_gradient_energy_continuous g f hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCI : Integrable C mu := hCc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDI : Integrable D mu := hDc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHI : Integrable (fun x => normGradSqFun g (fun y => h y*f y) x) mu :=
    (contMDiff_two_gradient_energy_continuous g _ hhf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hVI : Integrable (fun x => physicalPotential (n := n) p r x*(h x*f x)^2) mu :=
    (hVc.mul (hhf.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcancel : (∫ x, C x ∂mu) = -(∫ x, D x ∂mu) :=
    half_density_cross_term p hp r f hf
  have hpoint (x : sphere (0 : E) 1) :
      normGradSqFun g (fun y => h y*f y) x+physicalPotential (n := n) p r x*(h x*f x)^2 =
        rho x*normGradSqFun g f x+r/2*(C x+D x) := by
    rw [half_density_gradient_square p hp r f hf x]
    have hsq : (h x*f x)^2 = rho x*(f x)^2 := by
      rw [mul_pow,halfFactor_square]
      rfl
    rw [hsq]
    dsimp only [physicalPotential,C,D,rho]
    change Real.exp (r*t x)*(normGradSqFun g f x+
      r*f x*g.inner x (gradientFun g f x) (gradientFun g t x)+
      r^2/4*(1-(t x)^2)*(f x)^2)+
      (r^2/4*(1-(t x)^2)-(n : ℝ)*r/2*t x)*(Real.exp (r*t x)*(f x)^2) = _
    ring
  refine ⟨U,hU,?_,?_⟩
  · rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx]
    simp only [RCLike.inner_apply,conj_trivial]
    change (h x*f x)*(h x*f x) = rho x*(f x)^2
    rw [← pow_two,mul_pow,halfFactor_square]
    rfl
  · unfold potentialEnergy
    rw [hUE]
    have hpU : (∫ x, physicalPotential (n := n) p r x*(H1ComplToLp g U x)^2 ∂mu) =
        ∫ x, physicalPotential (n := n) p r x*(h x*f x)^2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [hU] with x hx
      rw [hx]
    rw [hpU]
    change (∫ x, normGradSqFun g (fun y => h y*f y) x ∂mu)+
      (∫ x, physicalPotential (n := n) p r x*(h x*f x)^2 ∂mu) = _
    rw [← integral_add hHI hVI]
    change (∫ x, normGradSqFun g (fun y => h y*f y) x+
      physicalPotential (n := n) p r x*(h x*f x)^2 ∂mu) = _
    rw [integral_congr_ae (Eventually.of_forall hpoint)]
    have hCDI : Integrable (fun x => C x+D x) mu := hCI.add hDI
    rw [integral_add (f := fun x => rho x*normGradSqFun g f x)
      (g := fun x => r/2*(C x+D x)) hGI (hCDI.const_mul (r/2)),integral_const_mul,
      integral_add (f := C) (g := D) hCI hDI,hcancel]
    change (∫ x, rho x*normGradSqFun g f x ∂mu)+
      r/2*(-(∫ x, D x ∂mu)+(∫ x, D x ∂mu)) = ∫ x, rho x*normGradSqFun g f x ∂mu
    ring

end DFLPhysicalHalfDensity
