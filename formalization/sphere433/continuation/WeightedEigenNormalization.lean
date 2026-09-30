import continuation.TransverseFirstMinimumUpper

/-! The original normalization of a genuine positive weighted eigenstate.
Mass, weighted mean and energy are obtained from the actual full H¹
half-density identity, then scaled by its positive mass. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere DFLPhysicalHalfDensity
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def scaleObservable (c : ℝ) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯) :
    C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯ :=
  ⟨fun x=>c*f x,contMDiff_const.mul f.contMDiff⟩

/-- Exact mass scaling in the original weighted variables. -/
theorem weightedMass_scale (p : E) (r c : ℝ) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯) :
    weightedMass (n := n) p r (scaleObservable c f)=c^2*weightedMass (n := n) p r f := by
  unfold weightedMass
  calc
    _=∫x,c^2*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change Real.exp (r*⟪p,(x : E)⟫_ℝ)*(c*f x)^2=c^2*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2)
        ring
    _=_ := integral_const_mul _ _

/-- Exact mean scaling in the original weighted variables. -/
theorem weightedMean_scale (p : E) (r c : ℝ) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯) :
    weightedMean (n := n) p r (scaleObservable c f)=c*weightedMean (n := n) p r f := by
  unfold weightedMean
  calc
    _=∫x,c*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change Real.exp (r*⟪p,(x : E)⟫_ℝ)*(c*f x)=c*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x)
        ring
    _=_ := integral_const_mul _ _

/-- Exact Dirichlet energy scaling follows from the true gradient rule. -/
theorem weightedEnergy_scale (p : E) (r c : ℝ) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯) :
    weightedEnergy (n := n) p r (scaleObservable c f)=c^2*weightedEnergy (n := n) p r f := by
  let g := roundMetric (E := E) (n := n)
  have hpt (x : sphere (0 : E) 1) : normGradSqFun g (scaleObservable c f) x=c^2*normGradSqFun g f x := by
    change g.inner x (gradientFun g (fun y=>c*f y) x) (gradientFun g (fun y=>c*f y) x)=
      c^2*g.inner x (gradientFun g f x) (gradientFun g f x)
    have hGr : gradientFun g (fun y=>c*f y) x=c • gradientFun g f x := by
      have hh := gradientFun_const_smul g c (f.contMDiff.mdifferentiable (by decide) x)
      have hfun : (c • (f : sphere (0 : E) 1 → ℝ))=(fun y=>c*f y) := by
        funext y; rfl
      rw [hfun] at hh
      exact hh
    rw [hGr]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  unfold weightedEnergy
  calc
    _=∫x,c^2*(Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun g f x)
      ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) g := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hpt]
        ring
    _=_ := integral_const_mul _ _

variable [NeZero n]

/-- Every actual nonzero positive eigenstate has positive original mass,
zero weighted mean and its exact eigenvalue-times-mass energy. -/
theorem actual_weighted_eigen_mass_mean_energy (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (hlam : 0<lam) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hfne : (f : sphere (0 : E) 1 → ℝ)≠0)
    (heig : ∀x,weightedRoundApply (n := n) p r f x=lam*f x) :
    0<weightedMass (n := n) p r f ∧ weightedMean (n := n) p r f=0 ∧
      weightedEnergy (n := n) p r f=lam*weightedMass (n := n) p r f := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨S,hSf,hSn,_hSe,hSo,hSE,_hSw⟩ := smooth_weighted_eigen_half_density
    (n := n) p hp r lam hlam.ne' f hfne heig
  obtain ⟨U,hU,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f
    (f.contMDiff.of_le (by decide))
  have hUg : U=smoothToH1Compl g S := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    filter_upwards [hU,S.memLp_two.coeFn_toLp] with x hx hs
    have hs' : smoothToLp g S x=S.toFun x := hs
    rw [hx,hs',hSf]
  have hm : weightedMass (n := n) p r f=‖smoothToLp g S‖^2 := by
    rw [hUg,H1ComplToLp_smoothToH1Compl] at hM
    exact hM.symm
  have hmean : weightedMean (n := n) p r f=0 := by
    have hh := completion_half_density_equilibrium_pairing p r f U hU
    rw [hUg,H1ComplToLp_smoothToH1Compl,hSo] at hh
    exact hh.symm
  have he : weightedEnergy (n := n) p r f=lam*weightedMass (n := n) p r f := by
    rw [hUg,physicalPotential_eq_drift,hSE] at hE
    rw [hm]
    exact hE.symm
  exact ⟨by rw [hm];exact sq_pos_of_pos hSn,hmean,he⟩

/-- Original mass normalization of any genuine nonzero positive eigenstate,
with a positive multiplier and the same actual eigenvalue energy. -/
theorem actual_weighted_eigen_normalized (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (hlam : 0<lam) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hfne : (f : sphere (0 : E) 1 → ℝ)≠0)
    (heig : ∀x,weightedRoundApply (n := n) p r f x=lam*f x) :
    ∃c : ℝ,0<c ∧ weightedMass (n := n) p r (scaleObservable c f)=1 ∧
      weightedMean (n := n) p r (scaleObservable c f)=0 ∧
      weightedEnergy (n := n) p r (scaleObservable c f)=lam := by
  obtain ⟨hM,hm,hE⟩ := actual_weighted_eigen_mass_mean_energy (n := n) p hp r lam hlam f hfne heig
  let m := weightedMass (n := n) p r f
  let c := (Real.sqrt m)⁻¹
  have hs : 0<Real.sqrt m := Real.sqrt_pos.mpr hM
  have hc : 0<c := inv_pos.mpr hs
  have hsq : (Real.sqrt m)^2=m := Real.sq_sqrt (show 0 ≤ m from hM.le)
  have hm0 : m ≠ 0 := hM.ne'
  have hcm : c^2*m=1 := by
    dsimp only [c]
    rw [inv_pow,hsq,inv_mul_cancel₀ hm0]
  refine ⟨c,hc,?_,?_,?_⟩
  · rw [weightedMass_scale]; exact hcm
  · rw [weightedMean_scale,hm,mul_zero]
  · rw [weightedEnergy_scale,hE]
    calc
      _=lam*(c^2*m) := by ring
      _=lam := by rw [hcm,mul_one]
end DFLPhysicalGap
