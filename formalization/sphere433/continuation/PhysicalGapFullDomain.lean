import continuation.PhysicalWeightedGap

/-! Agreement of the original C² weighted core minimum with the complete
actual H¹ half-density form domain. The comparison is between two attained
minima, using the manuscript's exact mass and energy transform. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLPhysicalHalfDensity
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The physical weighted gap is the attained first positive minimum of
its actual half-density operator on the complete H¹ domain. The equilibrium
and weak eigenidentity are actual states; no existence or domain premise
is supplied by the caller. -/
theorem actual_weighted_gap_full_H1_minimum (p : E) (hp : ‖p‖=1) (r : ℝ) :
    ∃ (e : SmoothScalar (roundMetric (E := E) (n := n)))
      (U : H1Compl (roundMetric (E := E) (n := n))),
      ‖smoothToLp (roundMetric (E := E) (n := n)) e‖=1 ∧ (∀ x,0<e.toFun x) ∧
      (∃ c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := n) p r) ∧
      ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖=1 ∧
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
        smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 ∧
      potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) U=
        weightedGap (n := n) p r ∧
      IsWeakPotentialEigenstate (roundMetric (E := E) (n := n)) (driftPotential n p r)
        (weightedGap (n := n) p r) U ∧
      ∀ W : H1Compl (roundMetric (E := E) (n := n)),
        ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
          smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 →
        weightedGap (n := n) p r*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
          potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨e,lam,u,hen,hep,_he0,hexp,_hl,hu,ho,heig,hmin,hweak⟩ :=
    actual_physical_drift_first_positive_exists (n := n) p hp r
  obtain ⟨c,hc,hce⟩ := hexp
  have hob : ⟪smoothToLp g u,smoothToLp g (driftBaselineSmooth (n := n) p r)⟫_ℝ=0 := by
    rw [hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),real_inner_smul_right] at ho
    exact (mul_eq_zero.mp ho).resolve_left hc.ne'
  let f := inverseHalfDensity (n := n) p r u.toContMDiffMap
  have hf (x : sphere (0 : E) 1) : halfFactor p r x*f x=u.toFun x := by
    change halfFactor p r x*(halfFactor p (-r) x*u.toFun x)=u.toFun x
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  obtain ⟨A,hA,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f
    (f.contMDiff.of_le (by decide))
  have hAu : A=smoothToH1Compl g u := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    filter_upwards [hA,u.memLp_two.coeFn_toLp] with x hx hy
    have hy' : smoothToLp g u x=u.toFun x := hy
    rw [hx,hy',hf]
  have hMf : weightedMass (n := n) p r f=1 := by
    rw [hAu,H1ComplToLp_smoothToH1Compl,hu] at hM
    norm_num at hM
    exact hM.symm
  have hmf : weightedMean (n := n) p r f=0 := by
    have hh := completion_half_density_equilibrium_pairing p r f A hA
    rw [hAu,H1ComplToLp_smoothToH1Compl,hob] at hh
    exact hh.symm
  have hq : potentialEnergy g (driftPotential n p r) (smoothToH1Compl g u)=lam := by
    have hw := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak g
      (driftPotential n p r) (driftPotential_memLp_top (n := n) p r) lam u heig
    have hh := hw (smoothToH1Compl g u)
    rw [actual_potential_form_diag,real_inner_self_eq_norm_sq,H1ComplToLp_smoothToH1Compl,hu] at hh
    simpa only [one_pow,mul_one] using hh
  have hEf : weightedEnergy (n := n) p r f=lam := by
    rw [hAu,physicalPotential_eq_drift,hq] at hE
    exact hE.symm
  obtain ⟨_,v,hvM,hvm,hvE,_,_,hvmin⟩ := actual_weighted_gap_spec (n := n) p hp r
  have hgapLE := hvmin f (f.contMDiff.of_le (by decide)) hmf
  rw [hMf,hEf,mul_one] at hgapLE
  obtain ⟨B,hB,hBM,hBE⟩ := half_density_exists_completion_mass_energy p hp r v
    (v.contMDiff.of_le (by decide))
  have hBo : ⟪H1ComplToLp g B,smoothToLp g e⟫_ℝ=0 := by
    have hh := completion_half_density_equilibrium_pairing p r v B hB
    change ⟪H1ComplToLp g B,smoothToLp g (driftBaselineSmooth (n := n) p r)⟫_ℝ=
      weightedMean (n := n) p r v at hh
    rw [hvm] at hh
    rw [hce,(ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r)),real_inner_smul_right,hh,mul_zero]
  have hlamLE := hmin B hBo
  rw [hBM,← physicalPotential_eq_drift,hBE] at hlamLE
  change lam*weightedMass (n := n) p r v≤weightedEnergy (n := n) p r v at hlamLE
  rw [hvM,hvE,mul_one] at hlamLE
  have heq : weightedGap (n := n) p r=lam := le_antisymm hgapLE hlamLE
  refine ⟨e,smoothToH1Compl g u,hen,hep,⟨c,hc,hce⟩,?_,?_,?_,?_,?_⟩
  · rw [H1ComplToLp_smoothToH1Compl]; exact hu
  · rw [H1ComplToLp_smoothToH1Compl]; exact ho
  · rw [heq]; exact hq
  · rw [heq]; exact hweak
  · rw [heq]; exact hmin

end DFLPhysicalGap
