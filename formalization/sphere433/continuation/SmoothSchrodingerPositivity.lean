import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Strong

/-! Stationary Schrödinger positivity from the actual parabolic strong maximum
principle. The elliptic equation is embedded as the time independent solution;
compactness supplies the required lower bound on the parabolic potential. -/

noncomputable section
open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DFLGroundPositivity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [VectorBundle ℝ E (TangentSpace I : M → Type _)]

/-- A nonzero smooth nonnegative stationary Schrödinger solution is strictly
positive everywhere on a connected closed manifold. -/
theorem smooth_schrodinger_nonnegative_strict_positive
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (V : M → ℝ) (hV : Continuous V) (lam : ℝ)
    (heig : ∀ x, ΔG g f x = (V x-lam)*f x)
    (hnn : ∀ x, 0 ≤ f x) (hnz : ∃ x, f x ≠ 0) :
    ∀ x, 0 < f x := by
  classical
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨x₀, hx₀⟩ := hnz
  have hanchor : 0 < f x₀ := lt_of_le_of_ne (hnn x₀) (Ne.symm hx₀)
  let X : ℝ → (x : M) → TangentSpace I x := fun _ _ => 0
  let P : ℝ → M → ℝ := fun _ x => lam-V x
  let u : ℝ → M → ℝ := fun _ x => f x
  have hucont : ContinuousOn (fun p : ℝ × M => u p.1 p.2)
      (spacetimeSlab (M := M) 1) :=
    (f.contMDiff.continuous.comp continuous_snd).continuousOn
  have hunn : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ u t x := fun _ _ x => hnn x
  have hutime : ∀ t ∈ Icc (0 : ℝ) 1, 0 < t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 1) t :=
    fun _ _ _ x => differentiableWithinAt_const (f x)
  have huspace : ∀ t ∈ Icc (0 : ℝ) 1, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) :=
    fun _ _ _ => f.contMDiff
  have husuper : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htpos : 0 < t) (x : M),
      0 ≤ derivWithin (fun s => u s x) (Icc 0 1) t -
        (ΔG g ⟨u t, huspace t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun g (u t) x)) - P t x*u t x := by
    intro t ht htpos x
    change 0 ≤ derivWithin (fun _ : ℝ => f x) (Icc 0 1) t -
      (ΔG g f x + g.inner x 0 (gradientFun g f x)) - (lam-V x)*f x
    have hd : derivWithin (fun _ : ℝ => f x) (Icc 0 1) t = 0 := by
      change derivWithin (Function.const ℝ (f x)) (Icc 0 1) t = 0
      rw [derivWithin_const]
      rfl
    rw [hd, map_zero, zero_apply, add_zero, heig]
    nlinarith
  have hPlower : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, lam-C ≤ P t x := by
    intro t ht x
    have hc := hC x (Set.mem_univ x)
    have hvc : V x ≤ C := (le_abs_self (V x)).trans (by simpa only [Real.norm_eq_abs] using hc)
    dsimp only [P]
    linarith
  intro y
  exact scalar_strong_maximum_principle_fixed_metric_with_drift_and_potential_positive
    g (by norm_num : (0 : ℝ) < 1) X (by norm_num : (0 : ℝ) ≤ 0)
    (fun _ _ _ => by simp [X]) P (lam-C) u hucont hunn hutime huspace husuper hPlower
    (t := 0) ⟨le_rfl, by norm_num⟩ hanchor y

omit [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
private theorem smooth_laplacian_const_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    ΔG g (c • f) x = c*ΔG g f x := by
  have hgrad : gradG g (c • f) = smoothSmul (fun _ : M => c) contMDiff_const (gradG g f) := by
    ext y
    rw [grad_g_apply, smoothSmul_apply, grad_g_apply]
    exact gradFun_const_smul g c (f.contMDiff.mdifferentiable (by simp) y)
  rw [Δ_g_def, hgrad, divergence_g_smoothSmul]
  simp only [tangentSectionAction_def, mfderiv_const, zero_apply, Δ_g_def]
  exact add_zero _

/-- A strictly positive smooth Schrödinger eigenfunction spans its entire
smooth eigenspace. The minimum of f/u and the strong maximum principle give
simplicity without a separate assumed ground-state uniqueness property. -/
theorem smooth_schrodinger_positive_eigenspace_simple
    (g : SmoothRiemannianMetric I M) (V : M → ℝ) (hV : Continuous V) (lam : ℝ)
    (u f : C^∞⟮I, M; ℝ⟯) (hu : ∀ x, 0 < u x)
    (heigu : ∀ x, ΔG g u x = (V x-lam)*u x)
    (heigf : ∀ x, ΔG g f x = (V x-lam)*f x) :
    ∃ c : ℝ, ∀ x, f x = c*u x := by
  classical
  have hratio : Continuous (fun x : M => f x/u x) :=
    f.contMDiff.continuous.div u.contMDiff.continuous (fun x => (hu x).ne')
  obtain ⟨x₀, _, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hratio.continuousOn
  let c : ℝ := f x₀/u x₀
  let h : C^∞⟮I, M; ℝ⟯ := f + (-c) • u
  have hnn : ∀ x, 0 ≤ h x := by
    intro x
    have hmin : c ≤ f x/u x := hx₀ (Set.mem_univ x)
    have hmul : c*u x ≤ f x := (le_div_iff₀ (hu x)).mp hmin
    change 0 ≤ f x + (-c)*u x
    linarith
  have hz₀ : h x₀ = 0 := by
    change f x₀ + (-(f x₀/u x₀))*u x₀ = 0
    field_simp [(hu x₀).ne']
    ring
  have heigh : ∀ x, ΔG g h x = (V x-lam)*h x := by
    intro x
    change ΔG g (f + (-c) • u) x = (V x-lam)*(f x+(-c)*u x)
    rw [Δ_g_add, smooth_laplacian_const_smul, heigf, heigu]
    ring
  have hzero : ∀ x, h x = 0 := by
    by_contra hn
    push Not at hn
    have hp := smooth_schrodinger_nonnegative_strict_positive g h V hV lam heigh hnn hn x₀
    rw [hz₀] at hp
    exact (lt_irrefl 0) hp
  refine ⟨c, fun x => ?_⟩
  have hz := hzero x
  change f x + (-c)*u x = 0 at hz
  linarith

end DFLGroundPositivity
