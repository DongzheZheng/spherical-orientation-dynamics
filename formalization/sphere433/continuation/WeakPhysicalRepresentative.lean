import continuation.PhysicalWeightedGap

/-! The true full H1 weak Schrödinger domain gives a smooth representative
in the original weighted physical variables. No regularity or Laplacian
domain membership is assumed for the initial completion state. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLPhysicalHalfDensity DFLPhysicalGap
namespace DFLWeakPhysical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The actual smooth scalar obtained by gauging a smooth weighted observable. -/
def weightedHalfDensitySmooth (p : E) (r : ℝ)
    (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯) :
    SmoothScalar (roundMetric (E := E) (n := n)) :=
  ⟨fun x => halfFactor p r x*f x,(halfFactor_smooth (n := n) p r).mul f.contMDiff⟩

/-- Every actual full-domain weak eigenstate has the same smooth weighted
representative, the true pointwise weighted PDE, and exact original mass
and Dirichlet energy. This also applies at eigenvalue zero. -/
theorem actual_gauged_weak_eigen_smooth_weighted_representative
    (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hU : IsWeakPotentialEigenstate (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) lam U) :
    ∃f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯,
      U=smoothToH1Compl (roundMetric (E := E) (n := n))
        (weightedHalfDensitySmooth p r f) ∧
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          (fun x => halfFactor p r x*f x) ∧
      (∀x,weightedRoundApply (n := n) p r f x=lam*f x) ∧
      weightedMass (n := n) p r f=‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 ∧
      weightedEnergy (n := n) p r f=lam*weightedMass (n := n) p r f := by
  let g := roundMetric (E := E) (n := n)
  let μ := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  have hUd : IsWeakPotentialEigenstate g (driftPotential n p r) lam U := by
    rw [← physicalPotential_eq_drift]
    exact hU
  obtain ⟨s,hUs,hsPDE⟩ := weak_smooth_potential_eigen_pointwise
    g (driftPotentialMap (n := n) p r) lam U hUd
  let f := inverseHalfDensity (n := n) p r s.toContMDiffMap
  have hf (x : sphere (0 : E) 1) : halfFactor p r x*f x=s.toFun x := by
    change halfFactor p r x*(halfFactor p (-r) x*s.toFun x)=s.toFun x
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  have hae : (H1ComplToLp g U : sphere (0 : E) 1 → ℝ)=ᵐ[μ]
      (fun x => halfFactor p r x*f x) := by
    rw [hUs,H1ComplToLp_smoothToH1Compl]
    exact s.memLp_two.coeFn_toLp.trans (Eventually.of_forall (fun x => (hf x).symm))
  have hGauge : U=smoothToH1Compl g (weightedHalfDensitySmooth p r f) := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    exact hae.trans (weightedHalfDensitySmooth p r f).memLp_two.coeFn_toLp.symm
  have hpoint : ∀x,weightedRoundApply (n := n) p r f x=lam*f x := by
    apply schrodinger_to_weighted_eigenfunction p hp r lam s.toContMDiffMap
    intro x
    rw [physicalPotential_eq_drift]
    exact hsPDE x
  obtain ⟨Z,hZ,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f
    (f.contMDiff.of_le (by decide))
  have hZU : Z=U := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    apply Lp.ext
    exact hZ.trans hae.symm
  have hV := driftPotential_memLp_top (n := n) p r
  have hQ : potentialEnergy g (driftPotential n p r) U=lam*‖H1ComplToLp g U‖^2 := by
    have hw : potentialForm (H1ComplToLp g)
        (boundedPotentialMultiplication (driftPotential n p r) hV) U U=
          lam*⟪H1ComplToLp g U,H1ComplToLp g U⟫_ℝ := by
      rw [actual_potential_form_eq]
      exact hUd U
    rw [actual_potential_form_diag,real_inner_self_eq_norm_sq] at hw
    exact hw
  rw [hZU] at hM hE
  have hMass : weightedMass (n := n) p r f=‖H1ComplToLp g U‖^2 := hM.symm
  have hEnergy : weightedEnergy (n := n) p r f=lam*weightedMass (n := n) p r f := by
    rw [physicalPotential_eq_drift,hQ] at hE
    exact hE.symm.trans (congrArg (fun z : ℝ => lam*z) hMass.symm)
  exact ⟨f,hGauge,hae,hpoint,hMass,hEnergy⟩

/-- Nonzero actual weak eigenvalues are orthogonal to the real equilibrium
baseline, by the original symmetric full-domain weak form. -/
theorem actual_weak_nonzero_eigen_equilibrium_orthogonal
    (p : E) (hp : ‖p‖=1) (r lam : ℝ) (hlam : lam≠0)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hU : IsWeakPotentialEigenstate (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) lam U) :
    ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
      smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth (n := n) p r)⟫_ℝ=0 := by
  let g := roundMetric (E := E) (n := n)
  let J := H1ComplToLp g
  let b := smoothToH1Compl g (driftBaselineSmooth (n := n) p r)
  have hV := driftPotential_memLp_top (n := n) p r
  let P := boundedPotentialMultiplication (driftPotential n p r) hV
  have hP := boundedPotentialMultiplication_symmetric (driftPotential n p r) hV
  have hzero : potentialForm J P b U=0 := driftBaseline_weak_zero p hp r U
  have hsym : potentialForm J P U b=potentialForm J P b U := by
    have hp' : ⟪P (J U),J b⟫_ℝ=⟪P (J b),J U⟫_ℝ :=
      (hP (J U) (J b)).trans (real_inner_comm _ _)
    simp only [potentialForm,hp',real_inner_comm U b,real_inner_comm (J U) (J b)]
  have hw : potentialForm J P U b=lam*⟪J U,J b⟫_ℝ := by
    rw [actual_potential_form_eq]
    rw [← physicalPotential_eq_drift]
    exact hU b
  rw [hsym,hzero] at hw
  have ho := (mul_eq_zero.mp hw.symm).resolve_left hlam
  simpa only [b,J,H1ComplToLp_smoothToH1Compl] using ho

/-- At a positive eigenvalue the same full H1 weak state has an actual
smooth weighted zero-mean representative with exact physical mass/energy. -/
theorem actual_gauged_weak_positive_eigen_representative
    (p : E) (hp : ‖p‖=1) (r lam : ℝ) (hlam : 0<lam)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hU : IsWeakPotentialEigenstate (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) lam U) :
    ∃f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯,
      U=smoothToH1Compl (roundMetric (E := E) (n := n))
        (weightedHalfDensitySmooth p r f) ∧
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          (fun x => halfFactor p r x*f x) ∧
      (∀x,weightedRoundApply (n := n) p r f x=lam*f x) ∧
      weightedMass (n := n) p r f=‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 ∧
      weightedEnergy (n := n) p r f=lam*weightedMass (n := n) p r f ∧
      weightedMean (n := n) p r f=0 := by
  obtain ⟨f,hUf,hae,hPDE,hM,hE⟩ := actual_gauged_weak_eigen_smooth_weighted_representative p hp r lam U hU
  have ho := actual_weak_nonzero_eigen_equilibrium_orthogonal p hp r lam hlam.ne' U hU
  have hh := completion_half_density_equilibrium_pairing p r f U hae
  rw [ho] at hh
  exact ⟨f,hUf,hae,hPDE,hM,hE,hh.symm⟩

end DFLWeakPhysical
