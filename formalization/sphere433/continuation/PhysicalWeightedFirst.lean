import continuation.HalfDensityEnergy
import continuation.PhysicalDriftFirstPositive
import continuation.OrthogonalStationarity

/-! The same actual first positive minimum in the physical weighted
variables. Its mass, mean, energy and comparison cover the original C²
sphere observables, with a full H¹ minimizer behind the construction. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
namespace DFLPhysicalHalfDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+1)] [NeZero n] in
theorem halfFactor_eq_baseline (p : E) (r : ℝ) (x : sphere (0 : E) 1) :
    halfFactor p r x = driftBaseline p r x := by
  unfold halfFactor driftBaseline
  congr 1
  ring

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+1)] [NeZero n] in
theorem physicalPotential_eq_drift (p : E) (r : ℝ) :
    physicalPotential (n := n) p r = driftPotential n p r := by
  funext x
  unfold physicalPotential driftPotential
  ring

omit [NeZero n] in
/-- Orthogonality to the actual half-density equilibrium is exactly the
original weighted zero-mean condition, including for C² completion states. -/
theorem completion_half_density_equilibrium_pairing (p : E) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (U : H1Compl (roundMetric (E := E) (n := n)))
    (hU : (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
      =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
        (fun x => halfFactor p r x*f x)) :
    ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
      smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth (n := n) p r)⟫_ℝ =
      ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
        ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let b := driftBaselineSmooth (n := n) p r
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hU,b.memLp_two.coeFn_toLp] with x hx hb
  have hbx : smoothToLp g b x = driftBaseline p r x := hb
  rw [hx,hbx]
  simp only [RCLike.inner_apply,conj_trivial]
  rw [← halfFactor_eq_baseline p r x]
  change halfFactor p r x*(halfFactor p r x*f x) = Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
  rw [← mul_assoc,← pow_two,halfFactor_square]

/-- A genuine normalized weighted eigenfunction attains the first positive
full-space minimum. The comparison uses every actual C² zero-mean test,
with neither a separation premise nor an assumed eigenstate existence. -/
theorem actual_weighted_first_positive_exists (p : E) (hp : ‖p‖ = 1) (r : ℝ) :
    ∃ (lam : ℝ) (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯), 0 < lam ∧
      (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2
        ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) = 1 ∧
      (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
        ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) = 0 ∧
      (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n)) f x
        ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) = lam ∧
      (∀ x, weightedRoundApply (n := n) p r f x = lam*f x) ∧
      (∃ x, f x ≠ 0) ∧
      ∀ (v : sphere (0 : E) 1 → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v →
        (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*v x
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) = 0 →
        lam*(∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(v x)^2
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) ≤
        ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n)) v x
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let mu := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  obtain ⟨e,lam,u,hen,hep,he0,hexp,hl,hu,ho,heig,hmin,_hweak⟩ :=
    actual_physical_drift_first_positive_exists (n := n) p hp r
  obtain ⟨c,hc,hce⟩ := hexp
  have hob : ⟪smoothToLp g u,smoothToLp g (driftBaselineSmooth (n := n) p r)⟫_ℝ = 0 := by
    rw [hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),real_inner_smul_right] at ho
    exact (mul_eq_zero.mp ho).resolve_left hc.ne'
  let f := inverseHalfDensity (n := n) p r u.toContMDiffMap
  have hf (x : sphere (0 : E) 1) : halfFactor p r x*f x = u.toFun x := by
    change halfFactor p r x*(halfFactor p (-r) x*u.toFun x) = u.toFun x
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  obtain ⟨U,hU,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f
    (f.contMDiff.of_le (by decide))
  have hUg : U = smoothToH1Compl g u := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    filter_upwards [hU,u.memLp_two.coeFn_toLp] with x hx hy
    have hy' : smoothToLp g u x = u.toFun x := hy
    rw [hx,hy',hf]
  have hnorm : (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2 ∂mu) = 1 := by
    rw [hUg,H1ComplToLp_smoothToH1Compl,hu] at hM
    norm_num at hM
    exact hM.symm
  have hmean : (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x ∂mu) = 0 := by
    have hh := completion_half_density_equilibrium_pairing p r f U hU
    rw [hUg,H1ComplToLp_smoothToH1Compl,hob] at hh
    exact hh.symm
  have hq : potentialEnergy g (driftPotential n p r) (smoothToH1Compl g u) = lam := by
    have hw := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak g
      (driftPotential n p r) (driftPotential_memLp_top (n := n) p r) lam u heig
    have hh := hw (smoothToH1Compl g u)
    rw [actual_potential_form_diag,real_inner_self_eq_norm_sq,H1ComplToLp_smoothToH1Compl,hu] at hh
    simpa only [one_pow,mul_one] using hh
  have he : (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun g f x ∂mu) = lam := by
    rw [hUg,physicalPotential_eq_drift,hq] at hE
    exact hE.symm
  have hpoint : ∀ x, weightedRoundApply (n := n) p r f x = lam*f x := by
    apply schrodinger_to_weighted_eigenfunction p hp r lam u.toContMDiffMap
    intro x
    rw [physicalPotential_eq_drift]
    exact heig x
  have hne : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2 ∂mu) = 0 := by
      simp only [h,zero_pow (by decide : 2 ≠ 0),mul_zero,integral_zero]
    linarith
  refine ⟨lam,f,hl,hnorm,hmean,he,hpoint,hne,?_⟩
  intro v hv hm
  obtain ⟨W,hW,hWM,hWE⟩ := half_density_exists_completion_mass_energy p hp r v hv
  have hWo : ⟪H1ComplToLp g W,smoothToLp g e⟫_ℝ = 0 := by
    have hh := completion_half_density_equilibrium_pairing p r v W hW
    rw [hm] at hh
    rw [hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),real_inner_smul_right,hh,mul_zero]
  have hh := hmin W hWo
  rw [hWM,← physicalPotential_eq_drift,hWE] at hh
  exact hh

end DFLPhysicalHalfDensity
