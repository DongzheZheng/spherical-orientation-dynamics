import DFLSphere433.RoundSphereCoordinates
import DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricShift
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Shape
import DifferentialGeometry.Geometry.Curvature.RoundSphere
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

/-! Equality in the actual round-sphere Lichnerowicz bound.
The proof uses the concrete Bochner identity, the actual metric Hessian,
and the ambient inclusion of the unit sphere. -/

noncomputable section
open Bundle Manifold Set Metric Module MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Integral.Measure

namespace DFLFirstEigenspace

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle

private theorem fin_two_sum
    {Idx : Type*} [Fintype Idx] (G : (Fin 2 → Idx) → Real) :
    (∑ a : Fin 2 → Idx, G a) =
      ∑ i : Idx, ∑ j : Idx, G (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  let etof : (Fin 2 → Idx) → Idx × Idx := fun a => (a 0, a 1)
  let einv : Idx × Idx → (Fin 2 → Idx) :=
    fun p a => if a = 0 then p.1 else p.2
  let e : (Fin 2 → Idx) ≃ Idx × Idx :=
    { toFun := etof
      invFun := einv
      left_inv := by
        intro a
        funext k
        fin_cases k <;> simp [etof, einv]
      right_inv := by
        rintro ⟨i, j⟩
        simp [etof, einv] }
  rw [Fintype.sum_equiv e G (fun p : Idx × Idx =>
    G (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro a
    congr 1
    change a = fun k : Fin 2 => if k = 0 then (etof a).1 else (etof a).2
    funext k
    fin_cases k <;> simp [etof]

section GeneralMetric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]

theorem hessian_norm_eq_chart
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  let hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  let cbasis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    chartBasisFamily (I := I) x hbase
  let cgInv : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  have hcinv : MetricInverseInBasis (I := I) g x cbasis cgInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, cbasis, cgInv,
        chartBasisFamily_apply] using hmatrix
  have hcb : ∀ i : Fin (Module.finrank Real E),
      cbasis i = centeredChartTangentBasis (I := I) x i := by
    intro i
    have hb : cbasis i = chartBasisVecFiber (I := I) x i x :=
      chartBasisFamily_apply (I := I) x hbase i
    rw [hb]
    exact chartBasisVecFiber_self (I := I) x i
  have hvec : ∀ i j : Fin (Module.finrank Real E),
      (fun a : Fin 2 => cbasis (if a = 0 then i else j)) = vec2 (cbasis i) (cbasis j) := by
    intro i j
    funext a
    fin_cases a <;> simp [vec2]
  have hcomp : ∀ i j : Fin (Module.finrank Real E),
      hessTensorAt (I := I) g f x (vec2 (cbasis i) (cbasis j)) =
        chartHessianTensor (I := I) g x f i j x := by
    intro i j
    rw [hessTensorAt_apply, hcb i, hcb j]
    rw [hessFun_eq_cov_grad (I := I) g f.contMDiff x
      (centeredChartTangentBasis (I := I) x i)
      (centeredChartTangentBasis (I := I) x j)]
    rw [← chartHessianTensor_eq_inner_cov_gradFun_basis_of_matrix_identity
      (I := I) g f.contMDiff x
      (chartHessianMatrixIdentity_holds (I := I) g f.contMDiff x) i j]
  rw [normSq0S_eq_coord (I := I) g x 2 cbasis cgInv hcinv
    (hessTensorAt (I := I) g f x)]
  unfold coordInner0S
  simp only [tensor0SComponent_apply]
  rw [chartHessFrobeniusSq_def, fin_two_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fin_two_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hprod :
      (∏ a : Fin 2, cgInv ((fun a' : Fin 2 => if a' = 0 then i else j) a)
        ((fun a' : Fin 2 => if a' = 0 then k else l) a)) = cgInv i k * cgInv j l := by
    rw [Fin.prod_univ_two]
    simp
  rw [hprod, hvec i j, hvec k l, hcomp i j, hcomp k l]


/-- The genuine metric Hessian defect has exactly the Bochner trace defect. -/
theorem hessian_defect_norm (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M)
    (heig : ΔG (I := I) g f x = -(Module.finrank ℝ E : ℝ) * f x) :
    normSq0S g x 2 (hessTensorAt g f x - (-f x) • metricTensor0S g x) =
      chartHessFrobeniusSq g f x - (Module.finrank ℝ E : ℝ)*(f x)^2 := by
  have htrace : metricTracePair0SAt g (hessTensorAt g f x) = ΔG g f x := by
    rw [← lap_eq_hess_on g isOpen_univ f.contMDiff.contMDiffOn (Set.mem_univ x)]
    exact laplacian_levi_eq g f.contMDiff x
  rw [normSq0S_sub_smul_metricTensor0S, hessian_norm_eq_chart, htrace, heig]
  ring

variable [CompactSpace M] [NeZero (Module.finrank ℝ E)]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Actual Bochner saturation on an Einstein manifold with unit curvature scale.
No Hessian identity or description of the first eigenspace is assumed. -/
theorem eigenvalue_dim_hessian (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯)
    (heig : ∀ x, ΔG g f x = -(Module.finrank ℝ E : ℝ) * f x)
    (hRic : ∀ x, ∀ v : TangentSpace I x,
      ricciTensor g x v v = ((Module.finrank ℝ E : ℝ)-1)*g.inner x v v) :
    ∀ x v w, hessFun g f x v w = -f x * g.inner x v w := by
  classical
  let μ := riemannianVolumeMeasure I M g
  let d : ℝ := Module.finrank ℝ E
  let N : M → ℝ := normGradSqFun g f
  let Hf : M → ℝ := chartHessFrobeniusSq g f
  have hN : ContMDiff I 𝓘(ℝ, ℝ) ∞ N := normGradSqFun_contMDiff g f.contMDiff
  have hH : Continuous Hf :=
    DifferentialGeometry.Analysis.Laplacian.chartHessFrobeniusSq_continuous g f.contMDiff
  have hfinite : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hNint : Integrable N μ := hN.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hHint : Integrable Hf μ := hH.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hfsq : Continuous (fun x : M => (f x)^2) := f.contMDiff.continuous.pow 2
  have hfsqint : Integrable (fun x : M => (f x)^2) μ :=
    hfsq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdelta : (ΔG g f : M → ℝ) = (-d) • (f : M → ℝ) := by
    funext x; exact heig x
  have hgradDelta : ∀ x : M, g.inner x (gradFun g f x) (gradFun g (ΔG g f) x) =
      -d*N x := by
    intro x
    rw [hdelta, Operator.gradFun_const_smul g (-d) (f.contMDiff.mdifferentiable (by simp) x)]
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rfl
  have hbochner : ∀ x, ΔG g ⟨N, hN⟩ x = 2*Hf x - 2*N x := by
    intro x
    have hb := bochner_pointwise_concrete_metric g f.contMDiff x
    change ΔG g ⟨N, hN⟩ x = 2*Hf x + 2*ricciTensor g x (gradFun g f x)
      (gradFun g f x) + 2*g.inner x (gradFun g f x) (gradFun g (ΔG g f) x) at hb
    rw [hRic, hgradDelta] at hb
    change ΔG g ⟨N, hN⟩ x = 2*Hf x + 2*((d-1)*N x) + 2*(-d*N x) at hb
    linarith
  have hLapZero : (∫ x, ΔG g ⟨N, hN⟩ x ∂μ) = 0 :=
    integral_divergence_eq_zero_of_compact g (gradG g ⟨N, hN⟩)
  have hBalance : (∫ x, Hf x ∂μ) = ∫ x, N x ∂μ := by
    have hInt : (∫ x, ΔG g ⟨N, hN⟩ x ∂μ) =
        2*(∫ x, Hf x ∂μ) - 2*(∫ x, N x ∂μ) := by
      calc
        _ = ∫ x, (2*Hf x - 2*N x) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hbochner)
        _ = _ := by
          rw [integral_sub (hHint.const_mul 2) (hNint.const_mul 2),
            integral_const_mul, integral_const_mul]
    linarith
  have hGreen : (∫ x, N x ∂μ) = d*(∫ x, (f x)^2 ∂μ) := by
    have hG : (∫ x, N x ∂μ) = -∫ x, f x * ΔG g f x ∂μ :=
      green_first_integral_inner_grad_eq_neg_integral_smul_laplacian g
        f.contMDiff f.contMDiff (HasCompactSupport.of_compactSpace _)
    have hpt : (fun x : M => f x * ΔG g f x) = fun x => -d*(f x)^2 := by
      funext x; rw [heig x]; dsimp only [d]; ring
    rw [hpt, integral_const_mul] at hG
    linarith
  have hdefint : Integrable (fun x => Hf x - d*(f x)^2) μ :=
    hHint.sub (hfsqint.const_mul d)
  have hdefzero : (∫ x, (Hf x - d*(f x)^2) ∂μ) = 0 := by
    rw [integral_sub hHint (hfsqint.const_mul d), integral_const_mul, hBalance, hGreen]
    ring
  have hdefnn : 0 ≤ᵐ[μ] (fun x => Hf x - d*(f x)^2) := by
    apply Filter.Eventually.of_forall
    intro x
    change 0 ≤ chartHessFrobeniusSq g f x - (Module.finrank ℝ E : ℝ)*(f x)^2
    rw [← hessian_defect_norm g f x (heig x)]
    exact normSq0S_nonneg g x 2 _
  have hdefae : (fun x => Hf x - d*(f x)^2) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae hdefnn hdefint).mp hdefzero
  have hdefcont : Continuous (fun x => Hf x - d*(f x)^2) :=
    hH.sub (continuous_const.mul hfsq)
  have hpos : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have heq := Measure.eqOn_open_of_ae_eq (μ := μ) (U := Set.univ)
    (f := fun x => Hf x - d*(f x)^2) (g := fun _ => (0 : ℝ))
    (by rw [Measure.restrict_univ]; exact hdefae) isOpen_univ
    hdefcont.continuousOn continuous_zero.continuousOn
  intro x v w
  have hnormzero : normSq0S g x 2
      (hessTensorAt g f x - (-f x) • metricTensor0S g x) = 0 := by
    rw [hessian_defect_norm g f x (heig x)]
    exact heq (Set.mem_univ x)
  have htensor : hessTensorAt g f x = (-f x) • metricTensor0S g x :=
    sub_eq_zero.mp ((normSq0S_eq_zero_iff g x 2 _).mp hnormzero)
  have happly := congrArg (fun T : Tensor0SSpace 2 I x => T (vec2 v w)) htensor
  simpa [hessTensorAt_apply, metricTensor0S_apply, vec2] using happly

end GeneralMetric

section Sphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private instance sphere_model_dim_pos : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]; infer_instance

private theorem sphere_connected_inst (hDim : 1 < finrank ℝ E) :
    ConnectedSpace (sphere (0 : E) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hDim

/-- Bochner saturation on the actual unit round sphere. -/
theorem round_eigenvalue_dim_hessian (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (heig : ∀ x, ΔG (roundMetric (E := E) (n := n)) f x = -(n : ℝ) * f x) :
    ∀ x v w, hessFun (roundMetric (E := E) (n := n)) f x v w =
      -f x * (roundMetric (E := E) (n := n)).inner x v w := by
  apply eigenvalue_dim_hessian
  · simpa only [finrank_euclideanSpace_fin] using heig
  · intro x v
    simpa only [finrank_euclideanSpace_fin] using ricciTensor_roundSphere x v v

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- Covariant gradient derivative obtained from the genuine Hessian equality. -/
theorem cov_grad_eq_neg_smul (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hess : ∀ x v w, hessFun (roundMetric (E := E) (n := n)) f x v w =
      -f x * (roundMetric (E := E) (n := n)).inner x v w)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    metricCov (roundMetric (E := E) (n := n))
      (fun p => gradFun (roundMetric (E := E) (n := n)) f p) x v = (-f x) • v := by
  let g := roundMetric (E := E) (n := n)
  let A := metricCov g (fun p => gradFun g f p) x v
  have hinner : ∀ w, g.inner x A w = -f x*g.inner x v w := by
    intro w
    change g.inner x ((LeviCivita g).toFun (fun p => gradFun g f p) x v) w = _
    rw [← hessFun_eq_cov_grad g f.contMDiff x v w]
    exact hess x v w
  apply sub_eq_zero.mp
  by_contra hne
  have hpos := g.pos x (A-(-f x) • v) hne
  have hz : g.inner x (A-(-f x) • v) (A-(-f x) • v) = 0 := by
    rw [(g.inner x).map_sub, sub_apply, (g.inner x).map_smul,
      smul_apply, smul_eq_mul, hinner]
    ring
  exact (ne_of_gt hpos) hz

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The ambient vector grad f + f x has zero derivative, by the actual Gauss formula. -/
theorem ambient_recovery_derivative_zero (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hess : ∀ x v w, hessFun (roundMetric (E := E) (n := n)) f x v w =
      -f x * (roundMetric (E := E) (n := n)).inner x v w) :
    ∀ x, mvfderiv (𝓡 n) (fun p =>
      dIncl (n := n) p (gradFun (roundMetric (E := E) (n := n)) f p) + f p • (p : E)) x = 0 := by
  let g := roundMetric (E := E) (n := n)
  let Y := fun p : sphere (0 : E) 1 => gradFun g f p
  have hY : ∀ x, MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (Y p)) x := by
    intro x
    exact (gradFun_contMDiff_total_section g f.contMDiff x).mdifferentiableAt (by simp)
  have hi : ∀ x, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    fun x => by
      have hicoe : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
          ((↑) : sphere (0 : E) 1 → E) x := contMDiff_coe_sphere.contMDiffAt
      exact hicoe.mdifferentiableAt (by simp)
  intro x
  ext v
  change mvfderiv (𝓡 n) (dInclField (n := n) Y +
    (f : sphere (0 : E) 1 → ℝ) • ((↑) : sphere (0 : E) 1 → E)) x v = 0
  rw [mvfderiv_add (dInclField_mdifferentiableAt (hY x))
    ((f.contMDiff.mdifferentiable (by simp) x).smul (hi x)),
    mvfderiv_smul (f.contMDiff.mdifferentiable (by simp) x) (hi x)]
  change ambDeriv (n := n) Y x v +
    (f x • dIncl (n := n) x v + mvfderiv (𝓡 n) f x v • (x : E)) = 0
  rw [ambDeriv_gauss (hY x) v, projConn_eq_metricCov (hY x) v,
    cov_grad_eq_neg_smul f hess x v, map_smul]
  have hdf : roundInner (n := n) x (Y x) v = mvfderiv (𝓡 n) f x v := by
    change g.inner x (gradFun g f x) v = _
    rw [inner_gradFun g f x v]
    rfl
  rw [hdf]
  module

/-- A genuine round-sphere Hessian equality recovers one constant ambient vector. -/
theorem hessian_eq_neg_metric_exists_linear
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hess : ∀ x v w, hessFun (roundMetric (E := E) (n := n)) f x v w =
      -f x * (roundMetric (E := E) (n := n)).inner x v w) :
    ∃ a : E, ∀ x : sphere (0 : E) 1, f x = ⟪a, (x : E)⟫ := by
  classical
  have hDim : 1 < finrank ℝ E := by
    rw [(Fact.out : finrank ℝ E = n + 1)]
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  let : ConnectedSpace (sphere (0 : E) 1) := sphere_connected_inst hDim
  let g := roundMetric (E := E) (n := n)
  let F : sphere (0 : E) 1 → E := fun p => dIncl (n := n) p (gradFun g f p) + f p • (p : E)
  have hF : MDifferentiable (𝓡 n) 𝓘(ℝ, E) F := by
    intro x
    have hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
        (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (gradFun g f p)) x :=
      (gradFun_contMDiff_total_section g f.contMDiff x).mdifferentiableAt (by simp)
    have hicoe : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        ((↑) : sphere (0 : E) 1 → E) x := contMDiff_coe_sphere.contMDiffAt
    exact (dInclField_mdifferentiableAt hY).add
      ((f.contMDiff.mdifferentiable (by simp) x).smul
        (hicoe.mdifferentiableAt (by simp)))
  have hFzero : ∀ x, mvfderiv (𝓡 n) F x = 0 :=
    ambient_recovery_derivative_zero f hess
  let x₀ : sphere (0 : E) 1 := Classical.choice inferInstance
  have hscalar : ∀ w : E, ∀ x, ⟪w, F x⟫ = ⟪w, F x₀⟫ := by
    intro w
    have hLC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (innerSL ℝ w) :=
      (innerSL ℝ w).contMDiff
    have hL : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (innerSL ℝ w) :=
      hLC.mdifferentiable (by simp)
    have hmd : MDifferentiable (𝓡 n) 𝓘(ℝ, ℝ) (fun x => ⟪w, F x⟫) := hL.comp hF
    have hzero : ∀ x, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x = 0 := by
      intro x
      ext v
      rw [mfderiv_inner_left w (hF x) v]
      change ⟪w, mvfderiv (𝓡 n) F x v⟫ = 0
      simp only [hFzero, zero_apply, inner_zero_right]
    have hlc := isLocallyConstant_of_mfderiv_eq_zero hmd hzero
    obtain ⟨c, hc⟩ := hlc.exists_eq_const
    intro x
    exact (congrFun hc x).trans (congrFun hc x₀).symm
  have hconst : ∀ x, F x = F x₀ := by
    intro x
    exact ext_inner_left ℝ (fun w => hscalar w x)
  refine ⟨F x₀, fun x => ?_⟩
  have hnormal : ⟪dIncl (n := n) x (gradFun g f x), (x : E)⟫ = 0 := by
    apply Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self (x : E))
    rw [← range_mvfderiv_subtypeVal (n := n) x]
    exact ⟨gradFun g f x, rfl⟩
  have hrec : ⟪F x, (x : E)⟫ = f x := by
    dsimp only [F]
    rw [inner_add_left, real_inner_smul_left, hnormal, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere x]
    ring
  rw [hconst x] at hrec
  exact hrec.symm

/-- Complete smooth first-eigenfunction rigidity, from the actual eigen-equation. -/
theorem round_first_eigenfunction_exists_linear
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (heig : ∀ x, ΔG (roundMetric (E := E) (n := n)) f x = -(n : ℝ) * f x) :
    ∃ a : E, ∀ x : sphere (0 : E) 1, f x = ⟪a, (x : E)⟫ :=
  hessian_eq_neg_metric_exists_linear f (round_eigenvalue_dim_hessian f heig)

/-- The entire smooth eigenspace at the first round-sphere eigenvalue is exactly
all restrictions of ambient linear functions, including the zero function. -/
theorem round_first_eigenfunction_iff_linear
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) :
    (∀ x, ΔG (roundMetric (E := E) (n := n)) f x = -(n : ℝ) * f x) ↔
      ∃ a : E, ∀ x : sphere (0 : E) 1, f x = ⟪a, (x : E)⟫ := by
  constructor
  · exact round_first_eigenfunction_exists_linear f
  · rintro ⟨a, ha⟩
    have hfun : f = innerCoordFun (E := E) (n := n) a := by
      ext x
      exact ha x
    rw [hfun]
    intro x
    exact DFLSpectralCoordinates.coordinate_laplacian x a

end Sphere
end DFLFirstEigenspace

