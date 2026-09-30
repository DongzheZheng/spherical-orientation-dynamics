import continuation.FullSphereFirstLower
import continuation.MeanSphereNormSplit
import continuation.MeanSphereEnergySplit
import continuation.WeightedMinimumRegularity
import continuation.ActualRadialCandidate
import continuation.CotTransversePiconeLower
import continuation.PhysicalWeightedGap
import continuation.PhysicalGapFullDomain
import continuation.TransverseFirstMinimumUpper

/-! Strict radial exclusion for the actual first physical eigenspace.
The genuine mean is a constrained minimizer; its derived smooth radial
PDE contradicts the proved strict radial/transverse ordering. -/
noncomputable section
set_option maxHeartbeats 1400000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLTransverseSphere
open DFLPhysicalHalfDensity DFLPhysicalGap DFLMeanSphere DFLPhysicalLatitude DFLCotSphere
namespace DFLFullSphereMeanZero
private local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def canonicalAxisSphere (k : ℕ) : sphere (0 : PhysicalAmbient k) 1 :=
  ⟨EuclideanSpace.single 0 1,by simp⟩

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

/-- The actual attained first minimum has no radial angular mean
in dimension at least two and positive field. -/
theorem attained_full_minimum_angular_mean_zero (k : ℕ) (hk : 1≤k) (r lam : ℝ) (hr : 0<r)
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
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=lam)
    (hupper : lam≤roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)) :
    ∀s : ℝ,cotMean (canonicalAxisSphere k) f s=0 := by
  let p := canonicalAxisSphere k
  let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
  change weightedMass (n := k+1) (p : PhysicalAmbient k) r f=1 at hM
  change weightedEnergy (n := k+1) (p : PhysicalAmbient k) r f=lam at hE
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
  have hAmin := full_minimum_comparison (p : PhysicalAmbient k) (by simp [p,canonicalAxisSphere]) r lam e hexp hmin A hAC2 hAm
  have hDmin := full_minimum_comparison (p : PhysicalAmbient k) (by simp [p,canonicalAxisSphere]) r lam e hexp hmin D hDC2 hDm
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
  have hz : ∀x : PhysicalSphere k,A x=0 := by
    by_contra hz
    push Not at hz
    obtain ⟨s,hsA,hseig⟩ := DFLWeightedMinimum.weighted_rayleigh_equality_smooth
      (p : PhysicalAmbient k) (by simp [p,canonicalAxisSphere]) r lam e hen he0 hexp hmin A hAC2 hAm hAeq
    have hlat : PhysicalConstantOnLatitudes k s := by
      intro x y hxy
      rw [hsA x,hsA y]
      change v ((physicalCoordinate k).toFun x)=v ((physicalCoordinate k).toFun y)
      rw [hxy]
    have hne : ∃x,s x≠0 := by
      obtain ⟨x,hx⟩ := hz
      exact ⟨x,by rw [hsA]; exact hx⟩
    have hstrict := DFLActualRadial.actual_radial_eigenvalue_gt_transverse_ground
      k hk r lam hr hlam.ne' s hlat hseig hne
    exact (not_lt_of_ge hupper) hstrict
  intro s
  let : Nontrivial (ℝ ∙ (p : PhysicalAmbient k))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := k) p)
  obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1) :
    (sphere (0 : (ℝ ∙ (p : PhysicalAmbient k))ᗮ) 1).Nonempty)
  exact (meanSphereProfile_cot (n := k) p f v hvs ⟨y,hy⟩ s).symm.trans (hz _)

/-- Every actual normalized smooth first minimum has zero actual angular
mean. The baseline and full-domain minimum are supplied by the proved
existence theorems, so no ground or form-domain premise remains. -/
theorem actual_gap_minimizer_angular_mean_zero (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hM : weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1)
    (hm : weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0)
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=
      weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) :
    ∀s : ℝ,cotMean (canonicalAxisSphere k) f s=0 := by
  let p : PhysicalAmbient k := EuclideanSpace.single 0 1
  let g := roundMetric (E := PhysicalAmbient k) (n := k+1)
  obtain ⟨e,_U,hen,_hep,hexp,_hn,_ho,_hq,_hw,hmin⟩ :=
    actual_weighted_gap_full_H1_minimum (n := k+1) p (by simp [p]) r
  obtain ⟨e0,he0n,_he0p,he00,hexp0,_horth⟩ :=
    actual_drift_normalized_zero_orthogonal_exists (n := k+1) p (by simp [p]) r
  obtain ⟨c,hc,hce⟩ := hexp
  obtain ⟨c0,hc0,hce0⟩ := hexp0
  have hcn : c*‖smoothToLp g (driftBaselineSmooth (n := k+1) p r)‖=1 := by
    rw [hce,ContinuousLinearMap.map_smul (smoothToLp g) c (driftBaselineSmooth (n := k+1) p r),norm_smul,Real.norm_eq_abs,abs_of_pos hc] at hen
    exact hen
  have hc0n : c0*‖smoothToLp g (driftBaselineSmooth (n := k+1) p r)‖=1 := by
    rw [hce0,ContinuousLinearMap.map_smul (smoothToLp g) c0 (driftBaselineSmooth (n := k+1) p r),norm_smul,Real.norm_eq_abs,abs_of_pos hc0] at he0n
    exact he0n
  have hbn : ‖smoothToLp g (driftBaselineSmooth (n := k+1) p r)‖≠0 := by
    intro hz
    rw [hz,mul_zero] at hcn
    norm_num at hcn
  have heeq : e=e0 := by
    have hcEq : c=c0 := mul_right_cancel₀ hbn (hcn.trans hc0n.symm)
    rw [hce,hce0,hcEq]
  have hen0 : ‖smoothToLp g e0‖=1 := by
    rw [heeq] at hen
    exact hen
  rw [heeq] at hmin
  have hgapPos := (actual_weighted_gap_spec (n := k+1) p (by simp [p]) r).1
  have hupper := actual_weighted_gap_le_transverse_of_unit_axis (n := k+1) p (by simp [p]) r
  exact attained_full_minimum_angular_mean_zero k hk r _ hr hgapPos e0 hen0 he00
    ⟨c0,hc0,hce0⟩ hmin f hM hm hE (by simpa only [Nat.cast_add,Nat.cast_one] using hupper)

end DFLFullSphereMeanZero
