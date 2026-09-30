import continuation.CompactPotentialDomain
import continuation.RoundSpherePositiveGround

/-! The manuscript's compact minimum, absolute-value contraction and
strong maximum principle, applied to any actual closed connected metric.
The same argument therefore covers the physical circle. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open DFLSphere
namespace DFLCompactPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (g : SmoothRiemannianMetric I M) : IsFiniteMeasure (volume g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
private local instance (g : SmoothRiemannianMetric I M) : (volume g).IsOpenPosMeasure :=
  riemannianVolumeMeasure_isOpenPosMeasure g

/-- Actual potential form on the full completed classical H1 space. -/
def potentialEnergy (g : SmoothRiemannianMetric I M) (V : M → ℝ)
    (U : H1Compl g) : ℝ :=
  ‖U‖^2-‖H1ComplToLp g U‖^2+∫ x, V x*(H1ComplToLp g U x)^2 ∂volume g

omit [NeZero (Module.finrank ℝ E)] in
theorem actual_potential_form_eq (g : SmoothRiemannianMetric I M) (V : M → ℝ)
    (hV : MemLp V ∞ (volume g)) (U W : H1Compl g) :
    potentialForm (H1ComplToLp g) (boundedPotentialMultiplication V hV) U W =
      ⟪U,W⟫_ℝ-⟪H1ComplToLp g U,H1ComplToLp g W⟫_ℝ+
        ∫ x, V x*H1ComplToLp g U x*H1ComplToLp g W x ∂volume g := by
  unfold potentialForm
  rw [boundedPotentialMultiplication_inner]

omit [NeZero (Module.finrank ℝ E)] in
theorem actual_potential_form_diag (g : SmoothRiemannianMetric I M) (V : M → ℝ)
    (hV : MemLp V ∞ (volume g)) (U : H1Compl g) :
    potentialForm (H1ComplToLp g) (boundedPotentialMultiplication V hV) U U =
      potentialEnergy g V U := by
  rw [actual_potential_form_eq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  unfold potentialEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- A real lowest eigenstate is derived from actual Rellich compactness. -/
theorem smooth_potential_ground_classical_exists (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (hJ0 : ∃ U : H1Compl g, H1ComplToLp g U ≠ 0) :
    ∃ (lam : ℝ) (u : SmoothScalar g), ‖smoothToLp g u‖ = 1 ∧
      potentialEnergy g V (smoothToH1Compl g u) = lam ∧
      (∀ W : H1Compl g, lam*‖H1ComplToLp g W‖^2 ≤ potentialEnergy g V W) ∧
      ∀ x : M, -ΔG g u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x := by
  have hVtop : MemLp (V : M → ℝ) ∞ (volume g) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨lam,U,hn,hw,hmin⟩ := compact_potential_form_ground_exists (H1ComplToLp g)
    (H1ComplToLp_isCompactOperator g) hJ0 (boundedPotentialMultiplication V hVtop)
    (boundedPotentialMultiplication_symmetric V hVtop)
  have hweak : IsWeakPotentialEigenstate g V lam U := by
    intro W
    have hh := hw W
    rw [actual_potential_form_eq] at hh
    exact hh
  obtain ⟨u,hU,hu⟩ := weak_smooth_potential_eigen_pointwise g V lam U hweak
  have he := hw U
  rw [actual_potential_form_diag,real_inner_self_eq_norm_sq,hn] at he
  refine ⟨lam,u,?_,?_,?_,hu⟩
  · rw [hU,H1ComplToLp_smoothToH1Compl] at hn
    exact hn
  · rw [hU] at he
    simpa using he
  · intro W
    simpa only [actual_potential_form_diag] using hmin W

variable [ConnectedSpace M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
/-- A normalized, strictly positive smooth lowest eigenfunction exists for
any actual smooth potential, with comparison against every true weak H¹ state. -/
theorem positive_smooth_potential_ground_exists (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (hJ0 : ∃ U : H1Compl g, H1ComplToLp g U ≠ 0) :
    ∃ (lam : ℝ) (u : SmoothScalar g),
      ‖smoothToLp g u‖ = 1 ∧
      (∀ x : M, 0 < u.toFun x) ∧
      potentialEnergy g V (smoothToH1Compl g u) = lam ∧
      (∀ W : H1Compl g,
        lam*‖H1ComplToLp g W‖^2 ≤ potentialEnergy g V W) ∧
      ∀ x : M,
        -ΔG g u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x := by
  obtain ⟨lam,f,hfnorm,hfe,hmin,_⟩ := smooth_potential_ground_classical_exists g V hJ0
  obtain ⟨A,hA,hAnorm,hAE⟩ := DFLAbsoluteH1.smooth_absolute_exists_completion g f
  have hn : ‖H1ComplToLp g A‖ = 1 := hAnorm.trans hfnorm
  have hpot : (∫ x, V x*(H1ComplToLp g A x)^2 ∂volume g) =
      ∫ x, V x*(H1ComplToLp g (smoothToH1Compl g f) x)^2 ∂volume g := by
    apply integral_congr_ae
    filter_upwards [hA,f.memLp_two.coeFn_toLp] with x ha hf
    have hff : H1ComplToLp g (smoothToH1Compl g f) x = f.toFun x := by
      rw [H1ComplToLp_smoothToH1Compl]
      exact hf
    rw [ha,hff,sq_abs]
  have he_le : potentialEnergy g V A ≤ lam := by
    unfold potentialEnergy
    rw [hpot]
    have hfE := h1_smooth_energy g f
    have hh := hfe
    unfold potentialEnergy at hh
    rw [hfE] at hh
    linarith
  have he : potentialEnergy g V A = lam := by
    have hlo := hmin A
    rw [hn] at hlo
    norm_num at hlo
    exact le_antisymm he_le hlo
  have hVtop : MemLp (V : M → ℝ) ∞ (volume g) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw := potentialForm_minimizer_weak (H1ComplToLp g)
    (boundedPotentialMultiplication V hVtop) (boundedPotentialMultiplication_symmetric V hVtop)
    lam A (by rw [actual_potential_form_diag,he,hn]; ring)
    (fun W => by rw [actual_potential_form_diag]; exact hmin W)
  have hweak : IsWeakPotentialEigenstate g V lam A := by
    intro W
    have hh := hw W
    rw [actual_potential_form_eq] at hh
    exact hh
  obtain ⟨u,hAu,hpoint⟩ := weak_smooth_potential_eigen_pointwise g V lam A hweak
  have hau : (H1ComplToLp g A : M → ℝ) =ᵐ[volume g] u.toFun := by
    rw [hAu,H1ComplToLp_smoothToH1Compl]
    exact u.memLp_two.coeFn_toLp
  have huf : u.toFun = fun x => |f.toFun x| :=
    MeasureTheory.Measure.eq_of_ae_eq (hau.symm.trans hA) u.smooth.continuous f.smooth.continuous.abs
  have hunn : ∀ x, 0 ≤ u.toFun x := by intro x; rw [huf]; exact abs_nonneg _
  have hun : ‖smoothToLp g u‖ = 1 := by rw [hAu,H1ComplToLp_smoothToH1Compl] at hn; exact hn
  have hunz : ∃ x, u.toFun x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : smoothToLp g u = 0 := by
      apply Lp.ext
      filter_upwards [u.memLp_two.coeFn_toLp,Lp.coeFn_zero ℝ 2 (volume g)] with x hx hzero
      have hxu : (smoothToLp g u : M → ℝ) x = u.toFun x := hx
      rw [hxu,h x,hzero]
      rfl
    rw [hz,norm_zero] at hun
    norm_num at hun
  have hu : ∀ x, 0 < u.toFun x :=
    DFLGroundPositivity.smooth_schrodinger_nonnegative_strict_positive g u.toContMDiffMap
      V V.contMDiff.continuous lam (fun x => by
        have hh := hpoint x
        change ΔG g u.toContMDiffMap x = (V x-lam)*u.toFun x
        nlinarith [hh])
      hunn hunz
  refine ⟨lam,u,hun,hu,?_,hmin,hpoint⟩
  rw [← hAu]
  exact he

omit [NeZero (Module.finrank ℝ E)] in
/-- Any strictly positive actual smooth eigenfunction spans the complete
smooth eigenspace for the same potential and eigenvalue. -/
theorem positive_potential_eigenspace_simple (g : SmoothRiemannianMetric I M)
    (V : M → ℝ) (hV : Continuous V) (lam : ℝ)
    (u f : SmoothScalar g)
    (hu : ∀ x, 0 < u.toFun x)
    (heigu : ∀ x, -ΔG g u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x)
    (heigf : ∀ x, -ΔG g f.toContMDiffMap x+V x*f.toFun x = lam*f.toFun x) :
    ∃ c : ℝ, ∀ x, f.toFun x = c*u.toFun x := by
  have heu : ∀ x, ΔG g u.toContMDiffMap x = (V x-lam)*u.toContMDiffMap x := by
    intro x
    change ΔG g u.toContMDiffMap x = (V x-lam)*u.toFun x
    nlinarith [heigu x]
  have hef : ∀ x, ΔG g f.toContMDiffMap x = (V x-lam)*f.toContMDiffMap x := by
    intro x
    change ΔG g f.toContMDiffMap x = (V x-lam)*f.toFun x
    nlinarith [heigf x]
  exact DFLGroundPositivity.smooth_schrodinger_positive_eigenspace_simple
    g V hV lam u.toContMDiffMap f.toContMDiffMap hu heu hef

/-- Simplicity covers the entire original distributional weak H¹ eigenspace:
regularity is a conclusion, and the state is a multiple of the positive ground. -/
theorem positive_potential_weak_eigenspace_simple (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (u : SmoothScalar g) (hu : ∀ x, 0 < u.toFun x)
    (heigu : ∀ x, -ΔG g u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x)
    (U : H1Compl g) (hU : IsWeakPotentialEigenstate g V lam U) :
    ∃ c : ℝ, U = c • smoothToH1Compl g u := by
  obtain ⟨f,hUf,hef⟩ := weak_smooth_potential_eigen_pointwise g V lam U hU
  obtain ⟨c,hf⟩ := positive_potential_eigenspace_simple g V V.contMDiff.continuous
    lam u f hu heigu hef
  have hfc : f = c • u := by
    apply SmoothScalar.ext
    funext x
    exact hf x
  refine ⟨c,?_⟩
  rw [hUf,hfc]
  exact (smoothToH1Compl g).map_smul c u

end DFLCompactPotential
