import continuation.TransverseSmoothGround
import continuation.PhysicalWeightedGap
import continuation.TiltDriftClassification

/-! The original physical transverse mode is an admissible trial state for
the genuine full H¹ first minimum. Its half-density transform satisfies
the actual weak eigen-equation and is orthogonal to the actual equilibrium.
The weighted C² gap and every weighted C² Rayleigh lower bound therefore
lie below the same unconditional auxiliary minimum. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline DFLPhysicalHalfDensity DFLPhysicalGap
namespace DFLTransverseSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

/-- The physical transverse auxiliary minimum is positive at every real
field, including zero field; no positive-eigenvalue premise is required. -/
theorem transverse_actual_minimum_pos (n : ℕ) [NeZero n] (r : ℝ) :
    0 < roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  by_cases hr : r=0
  · rw [hr,roundTiltMinimum_zero_field]
    exact hn
  · exact hn.trans (roundTiltMinimum_physical_above_baseline n (n : ℝ) r hr)

/-- Every nonzero smooth physical weighted eigenstate with nonzero
eigenvalue yields a nonzero actual half-density weak H¹ eigenstate,
orthogonal to the true equilibrium, with its exact energy. -/
theorem smooth_weighted_eigen_half_density (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (hlam : lam ≠ 0) (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hfne : (f : sphere (0 : E) 1 → ℝ) ≠ 0)
    (heig : ∀ x,weightedRoundApply (n := n) p r f x=lam*f x) :
    ∃ S : SmoothScalar (roundMetric (E := E) (n := n)),
      (∀ x,S.toFun x=halfFactor p r x*f x) ∧
      0<‖smoothToLp (roundMetric (E := E) (n := n)) S‖ ∧
      (∀ x,-ΔG (roundMetric (E := E) (n := n)) S.toContMDiffMap x+
        driftPotential n p r x*S.toFun x=lam*S.toFun x) ∧
      ⟪smoothToLp (roundMetric (E := E) (n := n)) S,
        smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth p r)⟫_ℝ=0 ∧
      potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r)
        (smoothToH1Compl (roundMetric (E := E) (n := n)) S)=
          lam*‖smoothToLp (roundMetric (E := E) (n := n)) S‖^2 ∧
      IsWeakPotentialEigenstate (roundMetric (E := E) (n := n)) (driftPotential n p r) lam
        (smoothToH1Compl (roundMetric (E := E) (n := n)) S) := by
  let g := roundMetric (E := E) (n := n)
  let S : SmoothScalar g := ⟨fun x => halfFactor p r x*f x,
    (halfFactor_smooth (n := n) p r).mul f.contMDiff⟩
  have hn : 0<‖smoothToLp g S‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hS : S=0 := smoothToLp_injective g (hz.trans (map_zero (smoothToLp g)).symm)
    apply hfne
    funext x
    have hh := congrArg (fun s : SmoothScalar g => s.toFun x) hS
    change halfFactor p r x*f x=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left (Real.exp_pos _).ne'
  have hs : ∀ x,-ΔG g S.toContMDiffMap x+driftPotential n p r x*S.toFun x=lam*S.toFun x := by
    intro x
    have hh := weighted_half_density_conjugacy p hp r f x
    rw [heig x,physicalPotential_eq_drift,
      laplacian_levi_eq g S.smooth] at hh
    change -ΔG g S.toContMDiffMap x+driftPotential n p r x*S.toFun x=lam*S.toFun x
    simpa only [S,SmoothScalar.toContMDiffMap] using hh.trans (by ring)
  have hw := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak g
    (driftPotential n p r) (driftPotential_memLp_top (n := n) p r) lam S hs
  let J := H1ComplToLp g
  let P := boundedPotentialMultiplication (driftPotential n p r) (driftPotential_memLp_top p r)
  have hP : P.IsSymmetric := boundedPotentialMultiplication_symmetric _ _
  have hsym (U W : H1Compl g) : potentialForm J P U W=potentialForm J P W U := by
    have hp' : ⟪P (J U),J W⟫_ℝ=⟪P (J W),J U⟫_ℝ :=
      (hP (J U) (J W)).trans (real_inner_comm _ _)
    simp only [potentialForm,hp',real_inner_comm U W,real_inner_comm (J U) (J W)]
  have ho : ⟪smoothToLp g S,smoothToLp g (driftBaselineSmooth p r)⟫_ℝ=0 := by
    have hh := hw (smoothToH1Compl g (driftBaselineSmooth p r))
    have hz := driftBaseline_weak_zero (n := n) p hp r (smoothToH1Compl g S)
    change potentialForm J P (smoothToH1Compl g S)
      (smoothToH1Compl g (driftBaselineSmooth p r))=lam*⟪J _,J _⟫_ℝ at hh
    rw [hsym,hz] at hh
    rw [H1ComplToLp_smoothToH1Compl,H1ComplToLp_smoothToH1Compl] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hlam
  have hE : potentialEnergy g (driftPotential n p r) (smoothToH1Compl g S)=
      lam*‖smoothToLp g S‖^2 := by
    have hh := hw (smoothToH1Compl g S)
    rw [actual_potential_form_diag,real_inner_self_eq_norm_sq,H1ComplToLp_smoothToH1Compl] at hh
    exact hh
  have hweak : IsWeakPotentialEigenstate g (driftPotential n p r) lam (smoothToH1Compl g S) := by
    intro W
    have hh := hw W
    rw [actual_potential_form_eq] at hh
    exact hh
  exact ⟨S,fun _ => rfl,hn,hs,ho,hE,hweak⟩

/-- The actual transverse candidate has positive weighted mass, zero
weighted mean and energy equal to the auxiliary minimum times its mass.
All integrals use the genuine physical round volume. -/
theorem actual_transverse_weighted_trial_exists (p a : E)
    (hp : ‖p‖=1) (ha : ‖a‖=1) (hpa : ⟪a,p⟫_ℝ=0) (r : ℝ) :
    ∃ f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯,
      0<weightedMass (n := n) p r f ∧ weightedMean (n := n) p r f=0 ∧
      weightedEnergy (n := n) p r f=
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*weightedMass (n := n) p r f ∧
      ∀ x,weightedRoundApply (n := n) p r f x=
        roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*f x := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨v,_hv,_hvp,_hvn,hsm,hne,heig⟩ := actual_transverse_smooth_ground_exists (n := n) p a hp ha hpa r
  let f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯ := ⟨transverseMode p a v,hsm⟩
  obtain ⟨S,hSf,hSn,_hSe,hSo,hSE,_hSw⟩ := smooth_weighted_eigen_half_density p hp r _
    (transverse_actual_minimum_pos n r).ne' f hne heig
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
  have he : weightedEnergy (n := n) p r f=
      roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2)*weightedMass (n := n) p r f := by
    rw [hUg,physicalPotential_eq_drift,hSE] at hE
    rw [hm]
    exact hE.symm
  exact ⟨f,by rw [hm];exact sq_pos_of_pos hSn,hmean,he,heig⟩

/-- Any full-H¹ Rayleigh lower bound on the true equilibrium-orthogonal
space is at most the actual transverse auxiliary minimum. -/
theorem fullH1_rayleigh_lower_le_transverse (p a : E)
    (hp : ‖p‖=1) (ha : ‖a‖=1) (hpa : ⟪a,p⟫_ℝ=0) (r lam : ℝ)
    (hmin : ∀ W : H1Compl (roundMetric (E := E) (n := n)),
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
        smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth p r)⟫_ℝ=0 →
      lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
        potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W) :
    lam≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  let g := roundMetric (E := E) (n := n)
  obtain ⟨v,_hv,_hp,_hn,hsm,hne,heig⟩ := actual_transverse_smooth_ground_exists (n := n) p a hp ha hpa r
  let f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯ := ⟨transverseMode p a v,hsm⟩
  obtain ⟨S,_hSf,hSn,_hSe,hSo,hSE,_hSw⟩ := smooth_weighted_eigen_half_density p hp r _
    (transverse_actual_minimum_pos n r).ne' f hne heig
  have hh := hmin (smoothToH1Compl g S) (by rw [H1ComplToLp_smoothToH1Compl];exact hSo)
  rw [H1ComplToLp_smoothToH1Compl,hSE] at hh
  exact le_of_mul_le_mul_right hh (sq_pos_of_pos hSn)

/-- The genuinely attained full-H¹ first positive eigenvalue satisfies
the original transverse upper bound, in every physical n≥1. -/
theorem actual_fullH1_first_positive_le_transverse_exists (p a : E)
    (hp : ‖p‖=1) (ha : ‖a‖=1) (hpa : ⟪a,p⟫_ℝ=0) (r : ℝ) :
    ∃ (e : SmoothScalar (roundMetric (E := E) (n := n))) (lam : ℝ)
      (u : SmoothScalar (roundMetric (E := E) (n := n))),
      ‖smoothToLp (roundMetric (E := E) (n := n)) e‖=1 ∧ (∀ x,0<e.toFun x) ∧
      (∀ x,-ΔG (roundMetric (E := E) (n := n)) e.toContMDiffMap x+
        driftPotential n p r x*e.toFun x=0) ∧
      (∃ c : ℝ,0<c ∧ e=c • driftBaselineSmooth (n := n) p r) ∧
      0<lam ∧ lam≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) ∧
      ‖smoothToLp (roundMetric (E := E) (n := n)) u‖=1 ∧
      ⟪smoothToLp (roundMetric (E := E) (n := n)) u,
        smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 ∧
      (∀ x,-ΔG (roundMetric (E := E) (n := n)) u.toContMDiffMap x+
        driftPotential n p r x*u.toFun x=lam*u.toFun x) ∧
      (∀ W : H1Compl (roundMetric (E := E) (n := n)),
        ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
          smoothToLp (roundMetric (E := E) (n := n)) e⟫_ℝ=0 →
        lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
          potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W) ∧
      IsWeakPotentialEigenstate (roundMetric (E := E) (n := n)) (driftPotential n p r) lam
        (smoothToH1Compl (roundMetric (E := E) (n := n)) u) := by
  obtain ⟨e,lam,u,hen,hep,he0,hexp,hl,hu,ho,he,hmin,hw⟩ :=
    actual_physical_drift_first_positive_exists (n := n) p hp r
  obtain ⟨c,hc,hce⟩ := hexp
  have hlo := fullH1_rayleigh_lower_le_transverse (n := n) p a hp ha hpa r lam (by
    intro W hW
    apply hmin W
    rw [hce,ContinuousLinearMap.map_smul (smoothToLp (roundMetric (E := E) (n := n)))
      c (driftBaselineSmooth (n := n) p r),real_inner_smul_right,hW,mul_zero])
  exact ⟨e,lam,u,hen,hep,he0,⟨c,hc,hce⟩,hl,hlo,hu,ho,he,hmin,hw⟩

/-- Every original C² weighted Rayleigh lower bound lies below the true
transverse minimum. No profile, zero-mean candidate, or mass hypothesis
is supplied: the actual smooth candidate is constructed in the proof. -/
theorem weightedC2_rayleigh_lower_le_transverse (p a : E)
    (hp : ‖p‖=1) (ha : ‖a‖=1) (hpa : ⟪a,p⟫_ℝ=0) (r lam : ℝ)
    (hmin : ∀ v : sphere (0 : E) 1 → ℝ,ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v →
      weightedMean (n := n) p r v=0 →
      lam*weightedMass (n := n) p r v ≤ weightedEnergy (n := n) p r v) :
    lam≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  obtain ⟨f,hM,hm,hE,_he⟩ := actual_transverse_weighted_trial_exists (n := n) p a hp ha hpa r
  have hh := hmin f (f.contMDiff.of_le (by decide)) hm
  rw [hE] at hh
  exact le_of_mul_le_mul_right hh hM

/-- The actual physical weighted C² gap has the original transverse
upper bound, valid on every Sⁿ with n≥1 and at every real field. -/
theorem actual_weighted_gap_le_transverse (p a : E)
    (hp : ‖p‖=1) (ha : ‖a‖=1) (hpa : ⟪a,p⟫_ℝ=0) (r : ℝ) :
    weightedGap (n := n) p r≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  obtain ⟨_hl,_f,_hM,_hm,_hE,_he,_hne,hmin⟩ := actual_weighted_gap_spec (n := n) p hp r
  exact weightedC2_rayleigh_lower_le_transverse (n := n) p a hp ha hpa r _ hmin

omit [FiniteDimensional ℝ E] in
/-- Every genuine unit axis on Sⁿ, n≥1, has an actual unit transverse
direction. It is a vector in the true orthogonal complement of the axis. -/
theorem unit_axis_exists_unit_transverse (n : ℕ) [Fact (finrank ℝ E=n+1)] [NeZero n]
    (p : E) (hp : ‖p‖=1) :
    ∃ a : E,‖a‖=1 ∧ ⟪a,p⟫_ℝ=0 := by
  have hpne : p≠0 := by intro h;rw [h,norm_zero] at hp;norm_num at hp
  let B := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hpne
  let i : Fin n := ⟨0,NeZero.pos n⟩
  let a : (ℝ ∙ p)ᗮ := B i
  exact ⟨a, B.norm_eq_one i,
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp a.property⟩

/-- The full-H¹ upper comparison needs only the original actual unit
axis; the transverse direction is supplied by sphere dimension n≥1. -/
theorem fullH1_rayleigh_lower_le_transverse_of_unit_axis (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (hmin : ∀ W : H1Compl (roundMetric (E := E) (n := n)),
      ⟪H1ComplToLp (roundMetric (E := E) (n := n)) W,
        smoothToLp (roundMetric (E := E) (n := n)) (driftBaselineSmooth p r)⟫_ℝ=0 →
      lam*‖H1ComplToLp (roundMetric (E := E) (n := n)) W‖^2 ≤
        potentialEnergy (roundMetric (E := E) (n := n)) (driftPotential n p r) W) :
    lam≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  obtain ⟨a,ha,hpa⟩ := unit_axis_exists_unit_transverse (n := n) p hp
  exact fullH1_rayleigh_lower_le_transverse p a hp ha hpa r lam hmin

/-- The original C² Rayleigh upper comparison needs no input transverse
vector or mode realizability condition. -/
theorem weightedC2_rayleigh_lower_le_transverse_of_unit_axis (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (hmin : ∀ v : sphere (0 : E) 1 → ℝ,ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v →
      weightedMean (n := n) p r v=0 →
      lam*weightedMass (n := n) p r v ≤ weightedEnergy (n := n) p r v) :
    lam≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  obtain ⟨a,ha,hpa⟩ := unit_axis_exists_unit_transverse (n := n) p hp
  exact weightedC2_rayleigh_lower_le_transverse p a hp ha hpa r lam hmin

/-- Unconditional upper bound for the original physical weighted gap.
Only the actual unit axis and real field are supplied. -/
theorem actual_weighted_gap_le_transverse_of_unit_axis (p : E) (hp : ‖p‖=1) (r : ℝ) :
    weightedGap (n := n) p r≤roundTiltMinimum n (n : ℝ) r ((n : ℝ)/2) := by
  obtain ⟨a,ha,hpa⟩ := unit_axis_exists_unit_transverse (n := n) p hp
  exact actual_weighted_gap_le_transverse (n := n) p a hp ha hpa r

end DFLTransverseSphere
