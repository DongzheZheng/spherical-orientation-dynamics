import DFLSphere433.RoundSpherePotentialGround
import DFLSphere433.H1ClosabilityAudit
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.ChartH2kRegularity
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
import DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.SmoothRepresentative

/-! Actual elliptic-domain and regularity bootstrap for the weak tilted
sphere eigenstate constructed by the fixed-form minimum argument. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace InnerProductSpace

namespace DFLSphere
open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- The actual full weak Schrödinger eigenidentity, before regularity. -/
def IsRoundWeakPotentialEigenstate (k : ℕ) (V : RoundSphere k → ℝ) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k)) : Prop :=
  ∀ W : H1Compl (roundSphereMetric k),
    ⟪U,W⟫_ℝ-⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ+
      (∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*
        H1ComplToLp (roundSphereMetric k) W x ∂roundVolume k) =
    lam*⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ

/-- The genuine source factor for `(1-Delta)u=(1+lambda-V)u`. -/
def smoothEigenSourceFactor (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ) :
    C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯ :=
  ⟨fun x => 1+lam-V x, contMDiff_const.sub V.contMDiff⟩

private theorem sourceFactor_L2_eq (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (hV : MemLp (V : RoundSphere k → ℝ) ∞ (roundVolume k))
    (f : Lp ℝ 2 (roundVolume k)) :
    smoothMulLp (roundSphereMetric k) (smoothEigenSourceFactor k V lam) f =
      (1+lam) • f-boundedPotentialMultiplication (V : RoundSphere k → ℝ) hV f := by
  apply Lp.ext
  filter_upwards [smoothMulLp_apply_coeFn (roundSphereMetric k) (smoothEigenSourceFactor k V lam) f,
    Lp.coeFn_sub ((1+lam) • f) (boundedPotentialMultiplication (V : RoundSphere k → ℝ) hV f),
    Lp.coeFn_smul (1+lam) f,
    boundedPotentialMultiplication_ae (V : RoundSphere k → ℝ) hV f] with x hs hsub hsm hp
  rw [hs,hsub]
  simp only [Pi.sub_apply]
  rw [hsm,hp]
  change (1+lam-V x)*f x = (1+lam)*f x-V x*f x
  ring

/-- The original weak eigenidentity places u in the real Laplacian domain;
no smoothness of u, domain membership, or regularity is an input. -/
theorem round_weak_smooth_potential_eigen_resolvent (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    U = resolvent (roundSphereMetric k)
      (smoothMulLp (roundSphereMetric k) (smoothEigenSourceFactor k V lam)
        (H1ComplToLp (roundSphereMetric k) U)) := by
  have hV : MemLp (V : RoundSphere k → ℝ) ∞ (roundVolume k) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ext_inner_right ℝ
  intro W
  rw [resolvent_inner_eq_lpFunctional,sourceFactor_L2_eq k V lam hV,
    inner_sub_right,real_inner_smul_right]
  have hp : ⟪H1ComplToLp (roundSphereMetric k) W,
      boundedPotentialMultiplication (V : RoundSphere k → ℝ) hV
        (H1ComplToLp (roundSphereMetric k) U)⟫_ℝ =
      ∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*
        H1ComplToLp (roundSphereMetric k) W x ∂roundVolume k := by
    calc
      _ = ⟪boundedPotentialMultiplication (V : RoundSphere k → ℝ) hV
        (H1ComplToLp (roundSphereMetric k) U),H1ComplToLp (roundSphereMetric k) W⟫_ℝ :=
        real_inner_comm _ _
      _ = _ := boundedPotentialMultiplication_inner _ _ _ _
  rw [hp]
  have hw := hU W
  have hc : ⟪H1ComplToLp (roundSphereMetric k) W,H1ComplToLp (roundSphereMetric k) U⟫_ℝ =
      ⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ :=
    real_inner_comm _ _
  rw [hc]
  linarith

theorem round_weak_smooth_potential_eigen_mem_laplacianDomain (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    U ∈ laplacianDomain (roundSphereMetric k) := by
  rw [laplacianDomain_mem_iff]
  exact ⟨_,round_weak_smooth_potential_eigen_resolvent k V lam U hU⟩

/-- The smooth source factor preserves the true Laplacian domain, giving
one additional genuine resolvent power without assuming u smooth. -/
theorem round_weak_smooth_potential_eigen_mem_domainPow_two (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    U ∈ laplacianDomainPow (roundSphereMetric k) 2 := by
  let Q := smoothEigenSourceFactor k V lam
  have hdom := round_weak_smooth_potential_eigen_mem_laplacianDomain k V lam U hU
  have hqdom := smoothMulH1Compl_mem_laplacianDomain (roundSphereMetric k) Q hdom
  obtain ⟨f,hf⟩ := (laplacianDomain_mem_iff (roundSphereMetric k)).mp hqdom
  rw [laplacianDomainPow_succ_mem_iff (roundSphereMetric k) 1]
  refine ⟨f,?_⟩
  rw [iteratedResolventL2_one]
  have hJQ := H1ComplToLp_smoothMulH1Compl (roundSphereMetric k) Q U
  rw [hf] at hJQ
  have he := round_weak_smooth_potential_eigen_resolvent k V lam U hU
  change U = resolvent (roundSphereMetric k) (smoothMulLp (roundSphereMetric k) Q
    (H1ComplToLp (roundSphereMetric k) U)) at he
  rw [← hJQ] at he
  exact he


private theorem round_eigen_preimage_eq (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U)
    (hdom : U ∈ laplacianDomain (roundSphereMetric k)) :
    laplacianDomain.preimage (roundSphereMetric k) ⟨U,hdom⟩ =
      smoothMulLp (roundSphereMetric k) (smoothEigenSourceFactor k V lam)
        (H1ComplToLp (roundSphereMetric k) U) := by
  apply resolvent_injective (roundSphereMetric k)
  rw [resolvent_laplacianDomain_preimage_eq]
  exact round_weak_smooth_potential_eigen_resolvent k V lam U hU

/-- Genuine all-order chart Sobolev regularity, obtained by the manuscript's
elliptic bootstrap with the smooth potential as the actual source multiplier. -/
theorem round_weak_smooth_potential_eigen_memWkpChart_all (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    ∀ m : ℕ, MemWkpChart (I := 𝓡 (k+2)) (M := RoundSphere k) m 2
      (H1ComplToLp (roundSphereMetric k) U : RoundSphere k → ℝ) := by
  let g := roundSphereMetric k
  let Q := smoothEigenSourceFactor k V lam
  have hpow := round_weak_smooth_potential_eigen_mem_domainPow_two k V lam U hU
  have hdom := laplacianDomainPow_succ_subset_laplacianDomain g 1 hpow
  have hpre := round_eigen_preimage_eq k V lam U hU hdom
  have h2 : MemWkpChart (I := 𝓡 (k+2)) (M := RoundSphere k) 2 2
      (H1ComplToLp g U : RoundSphere k → ℝ) := by
    have h1 : U ∈ laplacianDomainPow g 1 := by rw [laplacianDomainPow_one]; exact hdom
    exact (iteratedH2Regularity_one g h1).1
  have hsource (m : ℕ)
      (hu : MemWkpChart (I := 𝓡 (k+2)) (M := RoundSphere k) m 2
        (H1ComplToLp g U : RoundSphere k → ℝ)) :
      MemWkpChart (I := 𝓡 (k+2)) (M := RoundSphere k) m 2
        (laplacianDomain.preimage g ⟨U,hdom⟩ : RoundSphere k → ℝ) := by
    have hq := MemWkpChart_smooth_mul (by norm_num : (1 : ℝ≥0∞) ≤ 2) Q hu
    have hae : (laplacianDomain.preimage g ⟨U,hdom⟩ : RoundSphere k → ℝ) =ᵐ[roundVolume k]
        fun x => Q x*H1ComplToLp g U x := by
      rw [hpre]
      exact smoothMulLp_apply_coeFn g Q (H1ComplToLp g U)
    have hmeas : Measurable (laplacianDomain.preimage g ⟨U,hdom⟩ : RoundSphere k → ℝ) :=
      (laplacianDomain.preimage g ⟨U,hdom⟩).val.measurable
    have hmeasq : Measurable (fun x => Q x*H1ComplToLp g U x) :=
      Q.contMDiff.continuous.measurable.mul (H1ComplToLp g U).val.measurable
    have hc : ChartPushedAEEq (I := 𝓡 (k+2)) (M := RoundSphere k)
        (laplacianDomain.preimage g ⟨U,hdom⟩ : RoundSphere k → ℝ)
        (fun x => Q x*H1ComplToLp g U x) := by
      intro α
      exact chartPushed_aeEq_of_ae_eq_riemannianMeasure g α hmeas hmeasq hae
    exact (MemWkpChart_congr_chartPushed_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hc).2 hq
  have hall : ∀ m : ℕ, MemWkpChart (I := 𝓡 (k+2)) (M := RoundSphere k) (m+2) 2
      (H1ComplToLp g U : RoundSphere k → ℝ) := by
    intro m
    induction m with
    | zero => exact h2
    | succ m ih =>
      have hrhs := hsource (m+1) (MemWkpChart.le_of_le (by omega : m+1 ≤ m+2) ih)
      intro α
      exact chartPushed_memWkp_succ_jump g α (m+1) hpow ih hrhs
  intro m
  by_cases hm : m ≤ 2
  · exact MemWkpChart.le_of_le hm h2
  · have he : m-2+2 = m := by omega
    simpa only [he] using hall (m-2)

/-- A smooth representative is derived from the weak eigenidentity, rather
than supplied as a ground-state assumption. -/
theorem round_weak_smooth_potential_eigen_smooth_representative (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    ∃ s : SmoothScalar (roundSphereMetric k),
      (H1ComplToLp (roundSphereMetric k) U : RoundSphere k → ℝ) =ᵐ[roundVolume k] s.toFun := by
  have hall := round_weak_smooth_potential_eigen_memWkpChart_all k V lam U hU
  obtain ⟨f,hf,hae⟩ := DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall
    (roundSphereMetric k) (H1ComplToLp (roundSphereMetric k) U) (fun m => hall (2*m))
  exact ⟨⟨f,hf⟩,hae⟩

/-- The actual lowest Rayleigh value has a genuine smooth eigenstate
representative. Existence and regularity are both conclusions. -/
theorem round_smooth_potential_ground_exists (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ∃ (lam : ℝ) (U : H1Compl (roundSphereMetric k)) (s : SmoothScalar (roundSphereMetric k)),
      ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧
      roundPotentialEnergy k V U = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      IsRoundWeakPotentialEigenstate k V lam U ∧
      (H1ComplToLp (roundSphereMetric k) U : RoundSphere k → ℝ) =ᵐ[roundVolume k] s.toFun := by
  obtain ⟨lam,U,hn,he,hmin,hweak⟩ := round_potential_ground_exists k V V.contMDiff.continuous
  obtain ⟨s,hs⟩ := round_weak_smooth_potential_eigen_smooth_representative k V lam U hweak
  exact ⟨lam,U,s,hn,he,hmin,hweak,hs⟩


/-- The smooth representative satisfies the original pointwise Schrödinger
operator equation, with the actual round Laplacian and actual potential. -/
theorem round_weak_smooth_potential_eigen_pointwise (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    ∃ s : SmoothScalar (roundSphereMetric k),
      U = smoothToH1Compl (roundSphereMetric k) s ∧
      ∀ x : RoundSphere k,
        -ΔG (roundSphereMetric k) s.toContMDiffMap x+V x*s.toFun x = lam*s.toFun x := by
  let g := roundSphereMetric k
  let Q := smoothEigenSourceFactor k V lam
  obtain ⟨s,hs⟩ := round_weak_smooth_potential_eigen_smooth_representative k V lam U hU
  have hJs : H1ComplToLp g U = smoothToLp g s := by
    apply Lp.ext
    exact hs.trans s.memLp_two.coeFn_toLp.symm
  have hUs : U = smoothToH1Compl g s := by
    apply DFLSpectralUpstreamAudit.H1ComplToLp_injective g
    rw [H1ComplToLp_smoothToH1Compl]
    exact hJs
  let T : SmoothScalar g := ⟨fun x => Q x*s.toFun x,Q.contMDiff.mul s.smooth⟩
  have hmul : smoothMulLp g Q (smoothToLp g s) = smoothToLp g T := by
    apply Lp.ext
    filter_upwards [smoothMulLp_apply_coeFn g Q (smoothToLp g s),
      s.memLp_two.coeFn_toLp,T.memLp_two.coeFn_toLp] with x hq hx ht
    have hxs : smoothToLp g s x = s.toFun x := hx
    have hxt : smoothToLp g T x = T.toFun x := ht
    rw [hq,hxs,hxt]
  have hsrc : smoothToLp g s.oneSubLapClassical = smoothMulLp g Q (smoothToLp g s) := by
    apply resolvent_injective g
    rw [resolvent_smoothToLp_oneSubLapClassical,← hUs]
    have hh := round_weak_smooth_potential_eigen_resolvent k V lam U hU
    rw [hJs] at hh
    exact hh
  have hscalar : s.oneSubLapClassical = T := smoothToLp_injective g (hsrc.trans hmul)
  refine ⟨s,hUs,?_⟩
  intro x
  have he := congrArg (fun f : SmoothScalar g => f.toFun x) hscalar
  change s.toFun x-ΔG g s.toContMDiffMap x = (1+lam-V x)*s.toFun x at he
  nlinarith

/-- The genuine lowest Rayleigh value is attained by a smooth normalized
classical eigenfunction of the true round-sphere Schrödinger operator. -/
theorem round_smooth_potential_ground_classical_exists (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ∃ (lam : ℝ) (s : SmoothScalar (roundSphereMetric k)),
      ‖smoothToLp (roundSphereMetric k) s‖ = 1 ∧
      roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) s) = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      ∀ x : RoundSphere k,
        -ΔG (roundSphereMetric k) s.toContMDiffMap x+V x*s.toFun x = lam*s.toFun x := by
  obtain ⟨lam,U,hn,he,hmin,hweak⟩ := round_potential_ground_exists k V V.contMDiff.continuous
  obtain ⟨s,hUs,hpoint⟩ := round_weak_smooth_potential_eigen_pointwise k V lam U hweak
  rw [hUs,H1ComplToLp_smoothToH1Compl] at hn
  rw [hUs] at he
  exact ⟨lam,s,hn,he,hmin,hpoint⟩


/-- The exact manuscript tilt potential, now bundled as an actual smooth
function on the auxiliary round sphere. -/
def roundTiltSmoothPotential (k : ℕ) (lam0 r a : ℝ) :
    C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯ :=
  ⟨roundTiltPotential k lam0 r a,
    (contMDiff_const.add (contMDiff_const.mul
      (contMDiff_const.sub ((roundCoordinate k).smooth.pow 2)))).sub
      (contMDiff_const.mul (roundCoordinate k).smooth)⟩

/-- The original fixed-domain tilted ground is an actual normalized smooth
classical eigenstate; all real parameters are allowed. -/
theorem round_tilt_smooth_ground_classical_exists (k : ℕ) (lam0 r a : ℝ) :
    ∃ (lam : ℝ) (s : SmoothScalar (roundSphereMetric k)),
      ‖smoothToLp (roundSphereMetric k) s‖ = 1 ∧
      roundPotentialEnergy k (roundTiltPotential k lam0 r a)
        (smoothToH1Compl (roundSphereMetric k) s) = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤
          roundPotentialEnergy k (roundTiltPotential k lam0 r a) W) ∧
      ∀ x : RoundSphere k,
        -ΔG (roundSphereMetric k) s.toContMDiffMap x+
          roundTiltPotential k lam0 r a x*s.toFun x = lam*s.toFun x := by
  exact round_smooth_potential_ground_classical_exists k (roundTiltSmoothPotential k lam0 r a)

end DFLSphere
