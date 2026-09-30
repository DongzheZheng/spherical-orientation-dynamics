import continuation.MeanSphereNormSplit
import continuation.MeanSphereEnergySplit
import continuation.WeightedMinimumRegularity
import continuation.ActualRadialCandidate
import continuation.CotTransversePiconeLower
import continuation.PhysicalWeightedGap

/-! The original full physical minimum is bounded by the first transverse
minimum. Actual angular averaging, form orthogonality and constrained
stationarity produce the radial eigenstate when that component is nonzero. -/
noncomputable section
set_option maxHeartbeats 1400000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLPhysicalHalfDensity DFLPhysicalGap DFLMeanSphere DFLPhysicalLatitude DFLCotSphere
namespace DFLFullSphereFirst
private local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

private theorem full_minimum_comparison {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
    (p : E) (hp : ‖p‖=1) (r lam : ℝ) (e : SmoothScalar (roundMetric (E := E) (n := n)))
    (hexp : ∃c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := n) p r)
    (hmin : ∀W : H1Compl (roundMetric (E := E) (n := n)),
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 →
      lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2≤
        potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f)
    (hm : weightedMean (n := n) p r f=0) :
    lam*weightedMass (n := n) p r f≤weightedEnergy (n := n) p r f := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨U,hU,hM,hE⟩ := half_density_exists_completion_mass_energy p hp r f hf
  obtain ⟨c,hc,hce⟩ := hexp
  have horth : ⟪H1ComplToLp g U,smoothToLp g e⟫_ℝ=0 := by
    have hh := completion_half_density_equilibrium_pairing p r f U hU
    change _=weightedMean (n := n) p r f at hh
    rw [hm] at hh
    rw [hce,ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := n) p r),real_inner_smul_right,hh,mul_zero]
  have hh := hmin U horth
  rw [hM,← physicalPotential_eq_drift,hE] at hh
  exact hh

/-- The actual normalized full-H¹ first minimum lies above the original
first transverse minimum. Every separation and regularity premise is
proved from the genuine whole-sphere angular projection. -/
theorem attained_full_minimum_ge_transverse (k : ℕ) (hk : 1≤k) (r lam : ℝ) (hr : 0<r)
    (hlam : 0<lam) (e : SmoothScalar (roundMetric (E := PhysicalAmbient k) (n := k+1)))
    (hen : ‖smoothToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) e‖=1)
    (he0 : ∀x,-ΔG (roundMetric (E := PhysicalAmbient k) (n := k+1)) e.toContMDiffMap x+
      driftPotential (k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r x*e.toFun x=0)
    (hexp : ∃c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r)
    (hmin : ∀W : H1Compl (roundMetric (E := PhysicalAmbient k) (n := k+1)),
      ⟪H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) W,
        smoothToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) e⟫_ℝ=0 →
      lam*‖H1ComplToLp (roundMetric (E := PhysicalAmbient k) (n := k+1)) W‖^2≤
        potentialEnergy (roundMetric (E := PhysicalAmbient k) (n := k+1))
          (driftPotential (k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) W)
    (f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hM : weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1)
    (hm : weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0)
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=lam) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)≤lam := by
  let p : sphere (0 : PhysicalAmbient k) 1 := ⟨EuclideanSpace.single 0 1,by simp⟩
  let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
  obtain ⟨v,hv,hvs⟩ := angularMean_exists_C3_profile (n := k) p f
  let A := meanSphereProfile p v
  let D := fun x : PhysicalSphere k => f x-A x
  have hAC3 := meanSphereProfile_contMDiff (n := k) p v hv
  have hAC2 : ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) 2 A := hAC3.of_le (by norm_num)
  have hDC2 : ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) 2 D :=
    (f.contMDiff.of_le (by decide : (2 : ℕ∞ω)≤(∞ : ℕ∞ω))).sub hAC2
  have hAm : weightedMean (n := k+1) (p : PhysicalAmbient k) r A=0 := by
    have hh := meanSphereProfile_weighted_mean (n := k) p r f v hv hvs
    change weightedMean (n := k+1) (p : PhysicalAmbient k) r A=weightedMean (n := k+1) (p : PhysicalAmbient k) r f at hh
    exact hh.trans hm
  have hDm : weightedMean (n := k+1) (p : PhysicalAmbient k) r D=0 :=
    meanSphereProfile_deviation_weighted_mean (n := k) p r f v hv hvs
  have hAmin := full_minimum_comparison (p : PhysicalAmbient k) (by simp [p]) r lam e hexp hmin A hAC2 hAm
  have hDmin := full_minimum_comparison (p : PhysicalAmbient k) (by simp [p]) r lam e hexp hmin D hDC2 hDm
  have hMass := meanSphereProfile_weighted_mass_split (n := k) p r f v hv hvs
  change weightedMass (n := k+1) (p : PhysicalAmbient k) r f=
    weightedMass (n := k+1) (p : PhysicalAmbient k) r A+weightedMass (n := k+1) (p : PhysicalAmbient k) r D at hMass
  rw [hM] at hMass
  have hEnergy := meanSphere_weighted_energy_split (n := k) p r f v hv hvs
  change weightedEnergy (n := k+1) (p : PhysicalAmbient k) r f=
    weightedEnergy (n := k+1) (p : PhysicalAmbient k) r A+weightedEnergy (n := k+1) (p : PhysicalAmbient k) r D at hEnergy
  rw [hE] at hEnergy
  have hAeq : weightedEnergy (n := k+1) (p : PhysicalAmbient k) r A=
      lam*weightedMass (n := k+1) (p : PhysicalAmbient k) r A := by nlinarith
  by_cases hz : ∀x : PhysicalSphere k,A x=0
  · have hcot : ∀s : ℝ,cotMean p f s=0 := by
      intro s
      let : Nontrivial (ℝ ∙ (p : PhysicalAmbient k))ᗮ :=
        Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := k) p)
      obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1) :
        (sphere (0 : (ℝ ∙ (p : PhysicalAmbient k))ᗮ) 1).Nonempty)
      exact (meanSphereProfile_cot (n := k) p f v hvs ⟨y,hy⟩ s).symm.trans (hz _)
    have htransMass : (∫s : ℝ,cotTransverseMass p f r s)=
        weightedMass (n := k+1) (p : PhysicalAmbient k) r f := by
      unfold weightedMass
      rw [cot_sphere_weighted_norm (n := k) p r f]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [cot_transverse_mass_eq,integral_const_mul]
      apply congrArg (fun z : ℝ => cotScalarDensity k r s*z)
      apply integral_congr_ae
      filter_upwards [] with y
      change (f (cotSpherePD (n := k) p (y,s))-cotMean p f s)^2=(f (cotSpherePD (n := k) p (y,s)))^2
      rw [hcot,sub_zero]
    have hh := cot_weighted_energy_transverse_minimum_lower hk p f r
    rw [htransMass,hM,mul_one] at hh
    change _≤weightedEnergy (n := k+1) (p : PhysicalAmbient k) r f at hh
    rw [hE] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  · push Not at hz
    obtain ⟨s,hsA,hseig⟩ := DFLWeightedMinimum.weighted_rayleigh_equality_smooth
      (p : PhysicalAmbient k) (by simp [p]) r lam e hen he0 hexp hmin A hAC2 hAm hAeq
    have hlat : PhysicalConstantOnLatitudes k s := by
      intro x y hxy
      rw [hsA x,hsA y]
      change v ((physicalCoordinate k).toFun x)=v ((physicalCoordinate k).toFun y)
      rw [hxy]
    have hne : ∃x,s x≠0 := by
      obtain ⟨x,hx⟩ := hz
      exact ⟨x,by rw [hsA]; exact hx⟩
    exact DFLActualRadial.actual_radial_eigenvalue_ge_transverse_ground k r lam hr hlam.ne' s hlat hseig hne

/-- The manuscript's actual full weighted sphere gap, defined by its
original Rayleigh values, is bounded below by the actual transverse ground.
All full minimum, smoothness, and domain witnesses are constructed. -/
theorem actual_weighted_gap_ge_transverse (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)≤
      weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r := by
  let p : PhysicalAmbient k := EuclideanSpace.single 0 1
  let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
  obtain ⟨e,lam,u,hen,_hep,he0,hexp,hl,hu,ho,heig,hmin,_hweak⟩ :=
    actual_physical_drift_first_positive_exists (n := k+1) p (by simp [p]) r
  obtain ⟨c,hc,hce⟩ := hexp
  have hob : ⟪smoothToLp g u,smoothToLp g (driftBaselineSmooth (n := k+1) p r)⟫_ℝ=0 := by
    rw [hce,ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := k+1) p r),real_inner_smul_right] at ho
    exact (mul_eq_zero.mp ho).resolve_left hc.ne'
  let f := inverseHalfDensity (n := k+1) p r u.toContMDiffMap
  have hf (x : PhysicalSphere k) : halfFactor p r x*f x=u.toFun x := by
    change halfFactor p r x*(halfFactor p (-r) x*u.toFun x)=u.toFun x
    rw [← mul_assoc,halfFactor_cancel,one_mul]
  obtain ⟨U,hU,hM,hE⟩ := half_density_exists_completion_mass_energy p (by simp [p]) r f
    (f.contMDiff.of_le (by decide))
  have hUg : U=smoothToH1Compl g u := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    filter_upwards [hU,u.memLp_two.coeFn_toLp] with x hx hy
    have hy' : smoothToLp g u x=u.toFun x := hy
    rw [hx,hy',hf]
  have hMf : weightedMass (n := k+1) p r f=1 := by
    rw [hUg,H1ComplToLp_smoothToH1Compl,hu] at hM
    norm_num at hM
    exact hM.symm
  have hmf : weightedMean (n := k+1) p r f=0 := by
    have hh := completion_half_density_equilibrium_pairing p r f U hU
    rw [hUg,H1ComplToLp_smoothToH1Compl,hob] at hh
    exact hh.symm
  have hq : potentialEnergy g (driftPotential (k+1) p r) (smoothToH1Compl g u)=lam := by
    have hw := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak g
      (driftPotential (k+1) p r) (driftPotential_memLp_top (n := k+1) p r) lam u heig
    have hh := hw (smoothToH1Compl g u)
    rw [actual_potential_form_diag,real_inner_self_eq_norm_sq,H1ComplToLp_smoothToH1Compl,hu] at hh
    simpa only [one_pow,mul_one] using hh
  have hEf : weightedEnergy (n := k+1) p r f=lam := by
    rw [hUg,physicalPotential_eq_drift,hq] at hE
    exact hE.symm
  have hgap : weightedGap (n := k+1) p r=lam :=
    weighted_minimizer_identifies_gap p (by simp [p]) r lam f (f.contMDiff.of_le (by decide))
      hMf hmf hEf (full_minimum_comparison p (by simp [p]) r lam e ⟨c,hc,hce⟩ hmin)
  rw [hgap]
  exact attained_full_minimum_ge_transverse k hk r lam hr hl e hen he0 ⟨c,hc,hce⟩ hmin f hMf hmf hEf

end DFLFullSphereFirst
