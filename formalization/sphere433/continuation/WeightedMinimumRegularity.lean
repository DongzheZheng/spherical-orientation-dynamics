import continuation.PhysicalWeightedFirst

/-! Actual weighted Rayleigh equality in the full form domain implies the
original classical weighted PDE. The smooth representative is obtained by
the original constrained variation and elliptic bootstrap. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere DFLPhysicalHalfDensity
namespace DFLWeightedMinimum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- Equality in the original full-H¹ constrained minimum produces a
smooth representative of the same original weighted C² observable. -/
theorem weighted_rayleigh_equality_smooth (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (e : SmoothScalar (roundMetric (E := E) (n := n)))
    (hen : ‖smoothToLp (roundMetric (E := E) (n := n)) e‖=1)
    (he0 : ∀x,-ΔG (roundMetric (E := E) (n := n)) e.toContMDiffMap x+
      driftPotential n p r x*e.toFun x=0)
    (hexp : ∃c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := n) p r)
    (hmin : ∀W : H1Compl (roundMetric (E := E) (n := n)),
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
        smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 →
      lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
        potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f)
    (hm : (∫x,Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))=0)
    (heq : (∫x,Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n)) f x
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))=
        lam*(∫x,Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)))) :
    ∃s : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯,(∀x,s x=f x) ∧
      ∀x,weightedRoundApply (n := n) p r s x=lam*s x := by
  let g := roundMetric (E := E) (n := n)
  let μ := riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g
  let J := H1ComplToLp g
  have hV := driftPotential_memLp_top (n := n) p r
  let P := boundedPotentialMultiplication (driftPotential n p r) hV
  have hJe : J (smoothToH1Compl g e)=smoothToLp g e := H1ComplToLp_smoothToH1Compl g e
  obtain ⟨U,hU,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f hf
  obtain ⟨c,hc,hce⟩ := hexp
  have horth : ⟪J U,smoothToLp g e⟫_ℝ=0 := by
    have hh := completion_half_density_equilibrium_pairing p r f U hU
    rw [hm] at hh
    rw [hce,ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r),real_inner_smul_right,hh,mul_zero]
  have hweak0 := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak
    g (driftPotential n p r) hV 0 e (fun x => by simpa only [zero_mul] using he0 x)
  have hdiag : potentialForm J P U U=lam*‖J U‖^2 := by
    rw [actual_potential_form_diag,← physicalPotential_eq_drift,hE,hM]
    exact heq
  have hweak := orthogonal_potential_minimizer_weak J P
    (boundedPotentialMultiplication_symmetric _ _) (smoothToH1Compl g e) U
    (by rw [hJe]; exact hen)
    (fun W => by simpa only [zero_mul] using hweak0 W)
    (by simpa only [hJe] using horth) lam hdiag
    (fun W hW => by
      rw [actual_potential_form_diag]
      exact hmin W (by simpa only [hJe] using hW))
  have huw : IsWeakPotentialEigenstate g (driftPotential n p r) lam U := by
    intro W
    have hh := hweak W
    rw [actual_potential_form_eq] at hh
    exact hh
  obtain ⟨s,hUs,hsEq⟩ := weak_smooth_potential_eigen_pointwise g (driftPotentialMap (n := n) p r) lam U huw
  have hae : s.toFun =ᵐ[μ] fun x => halfFactor p r x*f x := by
    rw [hUs,H1ComplToLp_smoothToH1Compl] at hU
    exact s.memLp_two.coeFn_toLp.symm.trans hU
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hsfun : s.toFun=(fun x => halfFactor p r x*f x) :=
    MeasureTheory.Measure.eq_of_ae_eq hae s.smooth.continuous ((halfFactor_smooth (n := n) p r).continuous.mul hf.continuous)
  let q := inverseHalfDensity (n := n) p r s.toContMDiffMap
  have hq (x : sphere (0 : E) 1) : q x=f x := by
    change halfFactor p (-r) x*s.toFun x=f x
    rw [congrFun hsfun x,← mul_assoc]
    have hh := halfFactor_cancel p (-r) x
    simp only [neg_neg] at hh
    rw [hh,one_mul]
  refine ⟨q,hq,?_⟩
  apply schrodinger_to_weighted_eigenfunction p hp r lam s.toContMDiffMap
  intro x
  rw [physicalPotential_eq_drift]
  exact hsEq x

end DFLWeightedMinimum
