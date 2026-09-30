import continuation.ActualDriftBaseline

/-! Nonzero orthogonal trial states for the actual compact form domain.
Orthogonal projection removes the positive ground direction; two opposite
signs of a genuine coordinate prove the remainder is nonzero in actual L². -/
noncomputable section
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLSpectralCoordinates

namespace DFLPositiveOrthogonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Projecting a true sign-changing smooth trial state off a normalized
positive ground leaves a nonzero state in the actual full H¹ domain. -/
theorem positive_smooth_exists_nonzero_orthogonal (g : SmoothRiemannianMetric I M)
    (f t : SmoothScalar g) (hf : ‖smoothToLp g f‖ = 1) (hfpos : ∀ x, 0 < f.toFun x)
    (x y : M) (htx : 0 < t.toFun x) (hty : t.toFun y < 0) :
    ∃ U : H1Compl g, 0 < ‖H1ComplToLp g U‖ ∧
      ⟪H1ComplToLp g U,smoothToLp g f⟫_ℝ = 0 := by
  let J := H1ComplToLp g
  let c : ℝ := ⟪smoothToLp g t,smoothToLp g f⟫_ℝ
  let U := smoothToH1Compl g t-c • smoothToH1Compl g f
  have hJU : J U = smoothToLp g t-c • smoothToLp g f := by
    simp only [J,U,map_sub,map_smul,H1ComplToLp_smoothToH1Compl]
  have ho : ⟪J U,smoothToLp g f⟫_ℝ = 0 := by
    rw [hJU,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hf]
    dsimp [c]
    ring
  refine ⟨U,norm_pos_iff.mpr ?_,ho⟩
  intro hz
  have hLp : smoothToLp g t=c • smoothToLp g f :=
    sub_eq_zero.mp (hJU.symm.trans hz)
  let μ := riemannianVolumeMeasure I M g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hAE : t.toFun =ᵐ[μ] fun z => c*f.toFun z := by
    filter_upwards [t.memLp_two.coeFn_toLp,f.memLp_two.coeFn_toLp,
      Lp.coeFn_smul c (smoothToLp g f)] with z ht hf₁ hc
    have ht' : (smoothToLp g t : M → ℝ) z=t.toFun z := ht
    have hf' : (smoothToLp g f : M → ℝ) z=f.toFun z := hf₁
    have h := congrArg (fun q : Lp ℝ 2 μ => q z) hLp
    rw [hc] at h
    simpa only [Pi.smul_apply,smul_eq_mul,ht',hf'] using h
  have hfun := MeasureTheory.Measure.eq_of_ae_eq hAE t.smooth.continuous
    (continuous_const.mul f.smooth.continuous)
  have hx := congrFun hfun x
  have hy := congrFun hfun y
  have hcp : 0 < c := by nlinarith [hfpos x]
  have hp := mul_pos hcp (hfpos y)
  linarith

end DFLPositiveOrthogonal

namespace DFLDriftBaseline
open DFLPositiveOrthogonal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- Actual normalized positive zero mode and a genuinely nonzero orthogonal
trial state on physical Sⁿ, including the circle. No ground or orthogonal
state existence is assumed. -/
theorem actual_drift_normalized_zero_orthogonal_exists (p : E) (hp : ‖p‖ = 1) (r : ℝ) :
    ∃ s : SmoothScalar (roundMetric (E := E) (n := n)),
      ‖smoothToLp (roundMetric (E := E) (n := n)) s‖ = 1 ∧
      (∀ x, 0 < s.toFun x) ∧
      (∀ x, -ΔG (roundMetric (E := E) (n := n)) s.toContMDiffMap x+
        driftPotential n p r x*s.toFun x = 0) ∧
      (∃ c : ℝ, 0<c ∧ s=c • driftBaselineSmooth (n := n) p r) ∧
      ∃ U : H1Compl (roundMetric (E := E) (n := n)),
        0 < ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ∧
        ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
          smoothToLp (roundMetric (E := E) (n := n)) s⟫_ℝ = 0 := by
  let g := roundMetric (E := E) (n := n)
  let s₀ : SmoothScalar g := driftBaselineSmooth p r
  let x : sphere (0 : E) 1 := ⟨p,by rw [mem_sphere_zero_iff_norm]; exact hp⟩
  let y : sphere (0 : E) 1 := ⟨-p,by rw [mem_sphere_zero_iff_norm,norm_neg]; exact hp⟩
  have hs₀ : 0 < ‖smoothToLp g s₀‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hsz : s₀ = 0 := (smoothToLp_injective g)
      (hz.trans (map_zero (smoothToLp g)).symm)
    have hx := congrArg (fun q : SmoothScalar g => q.toFun x) hsz
    exact (driftBaseline_pos p r x).ne' hx
  let c : ℝ := ‖smoothToLp g s₀‖⁻¹
  have hc : 0 < c := inv_pos.mpr hs₀
  let s : SmoothScalar g := c • s₀
  have hsn : ‖smoothToLp g s‖ = 1 := by
    rw [show s = c • s₀ from rfl,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    exact inv_mul_cancel₀ hs₀.ne'
  have hspos : ∀ z, 0 < s.toFun z := by
    intro z
    change 0 < c*driftBaseline p r z
    exact mul_pos hc (driftBaseline_pos p r z)
  have heig : ∀ z, -ΔG g s.toContMDiffMap z+driftPotential n p r z*s.toFun z=0 := by
    intro z
    have hLap : ΔG g s.toContMDiffMap z=c*ΔG g s₀.toContMDiffMap z := by
      dsimp only [SmoothScalar.toContMDiffMap]
      rw [← laplacian_levi_eq g s.smooth,← laplacian_levi_eq g s₀.smooth]
      change laplacian (Geometry.Connection.LeviCivita g) g (c • s₀.toFun) z =
        c*laplacian (Geometry.Connection.LeviCivita g) g s₀.toFun z
      exact laplacian_const_smul (Geometry.Connection.LeviCivita g) g c
        (s₀.smooth.mdifferentiable (by simp))
        ((gradientFun_contMDiffAt_one g
          (s₀.smooth.contMDiffAt.of_le (by decide))).mdifferentiableAt (by norm_num))
    have hbase := driftBaseline_zero_eigen (n := n) p hp r z
    rw [laplacian_levi_eq g (driftBaseline_smooth (n := n) p r)] at hbase
    change -ΔG g s₀.toContMDiffMap z+driftPotential n p r z*s₀.toFun z=0 at hbase
    rw [hLap]
    change -(c*ΔG g s₀.toContMDiffMap z)+driftPotential n p r z*(c*s₀.toFun z)=0
    nlinarith [congrArg (fun q : ℝ => c*q) hbase]
  let t : SmoothScalar g := ⟨innerCoordFun (n := n) p,(innerCoordFun (n := n) p).contMDiff⟩
  have htx : 0 < t.toFun x := by
    change 0 < ⟪p,p⟫_ℝ
    rw [real_inner_self_eq_norm_sq,hp]
    norm_num
  have hty : t.toFun y < 0 := by
    change ⟪p,-p⟫_ℝ < 0
    rw [inner_neg_right,real_inner_self_eq_norm_sq,hp]
    norm_num
  exact ⟨s,hsn,hspos,heig,⟨c,hc,rfl⟩,
    positive_smooth_exists_nonzero_orthogonal g s t hsn hspos x y htx hty⟩

end DFLDriftBaseline
