import continuation.WeakPhysicalRepresentative
import continuation.PhysicalFirstEigenspace

/-! The original full H1 gauged weak first eigenspace, with the same fixed
positive latitude ground used for the actual classical first eigenspace.
Weak regularity and the reverse full-domain identity are proved. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLPhysicalHalfDensity DFLPhysicalGap DFLPhysicalLatitude DFL.Spectral
namespace DFLWeakPhysical
section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The actual classical weighted equation gauges back to the original
weak Schrödinger identity against every full H1 completion test. -/
theorem actual_smooth_weighted_eigen_gauged_weak (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hf : ∀x,weightedRoundApply (n := n) p r f x=lam*f x) :
    IsWeakPotentialEigenstate (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) lam
      (smoothToH1Compl (roundMetric (E := E) (n := n)) (weightedHalfDensitySmooth p r f)) := by
  let g := roundMetric (E := E) (n := n)
  let s := weightedHalfDensitySmooth p r f
  have hV : MemLp (physicalPotential (n := n) p r) ∞
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g) := by
    rw [physicalPotential_eq_drift]
    exact driftPotential_memLp_top p r
  have hs : ∀x,-ΔG g s.toContMDiffMap x+physicalPotential (n := n) p r x*s.toFun x=lam*s.toFun x := by
    intro x
    have hc := weighted_half_density_conjugacy p hp r f x
    change -laplacian (LeviCivita g) g s.toFun x+
      physicalPotential (n := n) p r x*s.toFun x=halfFactor p r x*weightedRoundApply (n := n) p r f x at hc
    have hLap : laplacian (LeviCivita g) g s.toFun x=ΔG g s.toContMDiffMap x :=
      laplacian_levi_eq g s.toContMDiffMap.contMDiff x
    rw [hLap,hf] at hc
    exact hc.trans (by change halfFactor p r x*(lam*f x)=lam*(halfFactor p r x*f x); ring)
  have hweak := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak
    g (physicalPotential (n := n) p r) hV lam s hs
  intro W
  rw [← actual_potential_form_eq g _ hV]
  exact hweak W

/-- An equilibrium-orthogonal equality state for the true full H1 first
Rayleigh bound satisfies the complete weak eigenidentity. The minimum and
normalized equilibrium are obtained from the proved original existence
theorem, and the equilibrium zero identity is the actual baseline identity. -/
theorem actual_full_H1_rayleigh_equality_weak (p : E) (hp : ‖p‖=1) (r : ℝ)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (horth : ⟪H1ComplToLp (roundMetric (E := E) (n := n)) U,
      smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth (n := n) p r)⟫_ℝ=0)
    (heq : potentialEnergy (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) U=
        weightedGap (n := n) p r*‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2) :
    IsWeakPotentialEigenstate (roundMetric (E := E) (n := n))
      (physicalPotential (n := n) p r) (weightedGap (n := n) p r) U := by
  let g := roundMetric (E := E) (n := n)
  let J := H1ComplToLp g
  let b := driftBaselineSmooth (n := n) p r
  let B := smoothToH1Compl g b
  have hV := driftPotential_memLp_top (n := n) p r
  let P := boundedPotentialMultiplication (driftPotential n p r) hV
  obtain ⟨e,_U0,hen,_hep,hexp,_hU0n,_hU0o,_hU0q,_hU0w,hmin⟩ :=
    actual_weighted_gap_full_H1_minimum (n := n) p hp r
  obtain ⟨c,_hc,hce⟩ := hexp
  have heq0 : ∀W : H1Compl g,potentialForm J P (smoothToH1Compl g e) W=0 := by
    intro W
    have hzero : potentialForm J P B W=0 := driftBaseline_weak_zero p hp r W
    rw [hce,(smoothToH1Compl g).map_smul c b]
    have hsplit : potentialForm J P (c • B) W=c*potentialForm J P B W := by
      simp only [potentialForm,map_smul,real_inner_smul_left]
      ring
    rw [hsplit,hzero,mul_zero]
  have hUo : ⟪J U,J (smoothToH1Compl g e)⟫_ℝ=0 := by
    rw [H1ComplToLp_smoothToH1Compl,hce,
      ContinuousLinearMap.map_smul (smoothToLp g) c b,real_inner_smul_right,horth,mul_zero]
  have hdiag : potentialForm J P U U=weightedGap (n := n) p r*‖J U‖^2 := by
    rw [actual_potential_form_diag,← physicalPotential_eq_drift]
    exact heq
  have hweak := orthogonal_potential_minimizer_weak J P
    (boundedPotentialMultiplication_symmetric _ _) (smoothToH1Compl g e) U
    (by rw [H1ComplToLp_smoothToH1Compl]; exact hen) heq0 hUo
    (weightedGap (n := n) p r) hdiag
    (fun W hW => by
      rw [actual_potential_form_diag]
      exact hmin W (by simpa only [J,H1ComplToLp_smoothToH1Compl] using hW))
  intro W
  have hh := hweak W
  rw [actual_potential_form_eq,← physicalPotential_eq_drift] at hh
  exact hh
end Generic

private local instance (k : ℕ) : MeasurableSpace (PhysicalSphere k) := borel (PhysicalSphere k)
private local instance (k : ℕ) : BorelSpace (PhysicalSphere k) := ⟨rfl⟩

/-- Every true full H1 weak first eigenstate has the given common ground
profile and one ambient transverse amplitude. Equality uses the original
L2 quotient and no smoothness hypothesis on the completion state. -/
theorem actual_gauged_weak_first_same_ground_mode (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (U : H1Compl (roundMetric (E := PhysicalAmbient k) (n := k+1)))
    (hU : IsWeakPotentialEigenstate (roundMetric (E := PhysicalAmbient k) (n := k+1))
      (physicalPotential (n := k+1) (EuclideanSpace.single 0 1) r) (physicalGap k r) U) :
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      (H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U : PhysicalSphere k → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
          (roundMetric (E := PhysicalAmbient k) (n := k+1))]
        (fun x => halfFactor (EuclideanSpace.single 0 1) r x*
          transverseMode (EuclideanSpace.single 0 1) a v x) := by
  obtain ⟨f,_hUf,hae,hf,_hM,_hE⟩ := actual_gauged_weak_eigen_smooth_weighted_representative
    (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r (physicalGap k r) U hU
  obtain ⟨a,ha,hrep⟩ := actual_first_eigen_same_ground_mode k hk r hr v hv hpos heig f hf
  refine ⟨a,ha,hae.trans ?_⟩
  exact Eventually.of_forall (fun x => congrArg (fun z : ℝ => halfFactor (EuclideanSpace.single 0 1) r x*z) (hrep x))

/-- Actual full-H1 equilibrium-orthogonal Rayleigh equality recovers the
same original transverse mode, without assuming a weak PDE or regularity. -/
theorem actual_full_H1_rayleigh_equality_same_ground_mode
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (U : H1Compl (roundMetric (E := PhysicalAmbient k) (n := k+1)))
    (horth : ⟪H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U,
      smoothToLp (roundMetric (E := PhysicalAmbient k) (n := k+1))
        (driftBaselineSmooth (n := k+1) (EuclideanSpace.single 0 1) r)⟫_ℝ=0)
    (heq : potentialEnergy (roundMetric (E := PhysicalAmbient k) (n := k+1))
      (physicalPotential (n := k+1) (EuclideanSpace.single 0 1) r) U=
        physicalGap k r*‖H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U‖^2) :
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      (H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U : PhysicalSphere k → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
          (roundMetric (E := PhysicalAmbient k) (n := k+1))]
        (fun x => halfFactor (EuclideanSpace.single 0 1) r x*
          transverseMode (EuclideanSpace.single 0 1) a v x) := by
  apply actual_gauged_weak_first_same_ground_mode k hk r hr v hv hpos heig U
  exact actual_full_H1_rayleigh_equality_weak (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) r U horth heq

/-- The original full gauged H1 weak first eigenidentity is equivalent to
the actual transverse form for the same specified positive ground. -/
theorem actual_gauged_weak_first_iff_mode (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
      (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v)
    (hSmooth : ∀a : PhysicalAmbient k,ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞
      (transverseMode (EuclideanSpace.single 0 1) a v))
    (U : H1Compl (roundMetric (E := PhysicalAmbient k) (n := k+1))) :
    IsWeakPotentialEigenstate (roundMetric (E := PhysicalAmbient k) (n := k+1))
      (physicalPotential (n := k+1) (EuclideanSpace.single 0 1) r) (physicalGap k r) U ↔
    ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
      (H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U : PhysicalSphere k → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
          (roundMetric (E := PhysicalAmbient k) (n := k+1))]
        (fun x => halfFactor (EuclideanSpace.single 0 1) r x*
          transverseMode (EuclideanSpace.single 0 1) a v x) := by
  constructor
  · exact actual_gauged_weak_first_same_ground_mode k hk r hr v hv hpos heig U
  · rintro ⟨a,ha,hae⟩
    let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
    let f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ :=
      ⟨transverseMode (EuclideanSpace.single 0 1) a v,hSmooth a⟩
    have hEq : LatitudeEigenEquation (k+1+2) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v := by
      simpa [Nat.add_assoc] using heig
    have hf : ∀x,weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r f x=physicalGap k r*f x := by
      intro x
      have h := transverseMode_weighted_eigen (n := k+1)
        (EuclideanSpace.single 0 1 : PhysicalAmbient k) a (by simp) ha r _ v hv hEq x
      change weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r
        (transverseMode (EuclideanSpace.single 0 1) a v) x=
          physicalGap k r*transverseMode (EuclideanSpace.single 0 1) a v x
      rw [actual_physical_gap_eq_transverse]
      simpa only [Nat.cast_add,Nat.cast_one] using h
    have hUf : U=smoothToH1Compl g (weightedHalfDensitySmooth (EuclideanSpace.single 0 1) r f) := by
      apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
      rw [H1ComplToLp_smoothToH1Compl]
      apply Lp.ext
      exact hae.trans (weightedHalfDensitySmooth (EuclideanSpace.single 0 1) r f).memLp_two.coeFn_toLp.symm
    rw [hUf]
    exact actual_smooth_weighted_eigen_gauged_weak (EuclideanSpace.single 0 1 : PhysicalAmbient k)
      (by simp) r (physicalGap k r) f hf

/-- One genuine positive normalized original ground identifies all states
of the actual full H1 weak first eigenspace, in both directions. -/
theorem actual_full_H1_first_eigenspace_common_ground_exists
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (k+3) r v=1 ∧
      LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v ∧
      (∀a : PhysicalAmbient k,ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞
        (transverseMode (EuclideanSpace.single 0 1) a v)) ∧
      ∀U : H1Compl (roundMetric (E := PhysicalAmbient k) (n := k+1)),
        IsWeakPotentialEigenstate (roundMetric (E := PhysicalAmbient k) (n := k+1))
          (physicalPotential (n := k+1) (EuclideanSpace.single 0 1) r) (physicalGap k r) U ↔
        ∃a : PhysicalAmbient k,⟪a,EuclideanSpace.single 0 1⟫_ℝ=0 ∧
          (H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) U : PhysicalSphere k → ℝ)
            =ᵐ[riemannianVolumeMeasure (𝓡 (k+1)) (PhysicalSphere k)
              (roundMetric (E := PhysicalAmbient k) (n := k+1))]
            (fun x => halfFactor (EuclideanSpace.single 0 1) r x*
              transverseMode (EuclideanSpace.single 0 1) a v x) := by
  obtain ⟨v,hv,hpos,hN,heig,hSmooth,_hClass,_hUnique,_hDim⟩ :=
    actual_first_eigenspace_common_ground_exists k hk r hr
  refine ⟨v,hv,hpos,hN,heig,hSmooth,?_⟩
  intro U
  exact actual_gauged_weak_first_iff_mode k hk r hr v hv hpos heig hSmooth U

end DFLWeakPhysical
