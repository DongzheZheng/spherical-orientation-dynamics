import continuation.RoundSphereGroundDomain
import continuation.CompactFirstPositive

/-! The original elliptic bootstrap for the full weak eigenidentity,
made independent of the auxiliary sphere's dimension convention.
In particular it can be used on the actual physical circle. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open DFLSphere
namespace DFLCompactPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
abbrev volume (g : SmoothRiemannianMetric I M) := riemannianVolumeMeasure I M g
private local instance (g : SmoothRiemannianMetric I M) : IsFiniteMeasure (volume g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

/-- The actual full weak Schrödinger eigenidentity, before regularity. -/
def IsWeakPotentialEigenstate (g : SmoothRiemannianMetric I M) (V : M → ℝ) (lam : ℝ)
    (U : H1Compl g) : Prop :=
  ∀ W : H1Compl g,
    ⟪U,W⟫_ℝ-⟪H1ComplToLp g U,H1ComplToLp g W⟫_ℝ+
      (∫ x, V x*H1ComplToLp g U x*
        H1ComplToLp g W x ∂volume g) =
    lam*⟪H1ComplToLp g U,H1ComplToLp g W⟫_ℝ

/-- The genuine source factor for `(1-Delta)u=(1+lambda-V)u`. -/
def smoothEigenSourceFactor (_g : SmoothRiemannianMetric I M) (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => 1+lam-V x, contMDiff_const.sub V.contMDiff⟩

omit [I.Boundaryless] in
private theorem sourceFactor_L2_eq (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (hV : MemLp (V : M → ℝ) ∞ (volume g))
    (f : Lp ℝ 2 (volume g)) :
    smoothMulLp g (smoothEigenSourceFactor g V lam) f =
      (1+lam) • f-boundedPotentialMultiplication (V : M → ℝ) hV f := by
  apply Lp.ext
  filter_upwards [smoothMulLp_apply_coeFn g (smoothEigenSourceFactor g V lam) f,
    Lp.coeFn_sub ((1+lam) • f) (boundedPotentialMultiplication (V : M → ℝ) hV f),
    Lp.coeFn_smul (1+lam) f,
    boundedPotentialMultiplication_ae (V : M → ℝ) hV f] with x hs hsub hsm hp
  rw [hs,hsub]
  simp only [Pi.sub_apply]
  rw [hsm,hp]
  change (1+lam-V x)*f x = (1+lam)*f x-V x*f x
  ring

/-- The original weak eigenidentity places u in the real Laplacian domain;
no smoothness of u, domain membership, or regularity is an input. -/
theorem weak_smooth_potential_eigen_resolvent (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    U = resolvent g
      (smoothMulLp g (smoothEigenSourceFactor g V lam)
        (H1ComplToLp g U)) := by
  have hV : MemLp (V : M → ℝ) ∞ (volume g) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ext_inner_right ℝ
  intro W
  rw [resolvent_inner_eq_lpFunctional,sourceFactor_L2_eq g V lam hV,
    inner_sub_right,real_inner_smul_right]
  have hp : ⟪H1ComplToLp g W,
      boundedPotentialMultiplication (V : M → ℝ) hV
        (H1ComplToLp g U)⟫_ℝ =
      ∫ x, V x*H1ComplToLp g U x*
        H1ComplToLp g W x ∂volume g := by
    calc
      _ = ⟪boundedPotentialMultiplication (V : M → ℝ) hV
        (H1ComplToLp g U),H1ComplToLp g W⟫_ℝ :=
        real_inner_comm _ _
      _ = _ := boundedPotentialMultiplication_inner _ _ _ _
  rw [hp]
  have hw := hU W
  have hc : ⟪H1ComplToLp g W,H1ComplToLp g U⟫_ℝ =
      ⟪H1ComplToLp g U,H1ComplToLp g W⟫_ℝ :=
    real_inner_comm _ _
  rw [hc]
  linarith

theorem weak_smooth_potential_eigen_mem_laplacianDomain (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    U ∈ laplacianDomain g := by
  rw [laplacianDomain_mem_iff]
  exact ⟨_,weak_smooth_potential_eigen_resolvent g V lam U hU⟩

/-- The smooth source factor preserves the true Laplacian domain, giving
one additional genuine resolvent power without assuming u smooth. -/
theorem weak_smooth_potential_eigen_mem_domainPow_two (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    U ∈ laplacianDomainPow g 2 := by
  let Q := smoothEigenSourceFactor g V lam
  have hdom := weak_smooth_potential_eigen_mem_laplacianDomain g V lam U hU
  have hqdom := smoothMulH1Compl_mem_laplacianDomain g Q hdom
  obtain ⟨f,hf⟩ := (laplacianDomain_mem_iff g).mp hqdom
  rw [laplacianDomainPow_succ_mem_iff g 1]
  refine ⟨f,?_⟩
  rw [iteratedResolventL2_one]
  have hJQ := H1ComplToLp_smoothMulH1Compl g Q U
  rw [hf] at hJQ
  have he := weak_smooth_potential_eigen_resolvent g V lam U hU
  change U = resolvent g (smoothMulLp g Q
    (H1ComplToLp g U)) at he
  rw [← hJQ] at he
  exact he


private theorem eigen_preimage_eq (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U)
    (hdom : U ∈ laplacianDomain g) :
    laplacianDomain.preimage g ⟨U,hdom⟩ =
      smoothMulLp g (smoothEigenSourceFactor g V lam)
        (H1ComplToLp g U) := by
  apply resolvent_injective g
  rw [resolvent_laplacianDomain_preimage_eq]
  exact weak_smooth_potential_eigen_resolvent g V lam U hU

variable [NeZero (Module.finrank ℝ E)]

/-- Genuine all-order chart Sobolev regularity, obtained by the manuscript's
elliptic bootstrap with the smooth potential as the actual source multiplier. -/
theorem weak_smooth_potential_eigen_memWkpChart_all (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    ∀ m : ℕ, MemWkpChart (I := I) (M := M) m 2
      (H1ComplToLp g U : M → ℝ) := by
  let Q := smoothEigenSourceFactor g V lam
  have hpow := weak_smooth_potential_eigen_mem_domainPow_two g V lam U hU
  have hdom := laplacianDomainPow_succ_subset_laplacianDomain g 1 hpow
  have hpre := eigen_preimage_eq g V lam U hU hdom
  have h2 : MemWkpChart (I := I) (M := M) 2 2
      (H1ComplToLp g U : M → ℝ) := by
    have h1 : U ∈ laplacianDomainPow g 1 := by rw [laplacianDomainPow_one]; exact hdom
    exact (iteratedH2Regularity_one g h1).1
  have hsource (m : ℕ)
      (hu : MemWkpChart (I := I) (M := M) m 2
        (H1ComplToLp g U : M → ℝ)) :
      MemWkpChart (I := I) (M := M) m 2
        (laplacianDomain.preimage g ⟨U,hdom⟩ : M → ℝ) := by
    have hq := MemWkpChart_smooth_mul (by norm_num : (1 : ℝ≥0∞) ≤ 2) Q hu
    have hae : (laplacianDomain.preimage g ⟨U,hdom⟩ : M → ℝ) =ᵐ[volume g]
        fun x => Q x*H1ComplToLp g U x := by
      rw [hpre]
      exact smoothMulLp_apply_coeFn g Q (H1ComplToLp g U)
    have hmeas : Measurable (laplacianDomain.preimage g ⟨U,hdom⟩ : M → ℝ) :=
      (laplacianDomain.preimage g ⟨U,hdom⟩).val.measurable
    have hmeasq : Measurable (fun x => Q x*H1ComplToLp g U x) :=
      Q.contMDiff.continuous.measurable.mul (H1ComplToLp g U).val.measurable
    have hc : ChartPushedAEEq (I := I) (M := M)
        (laplacianDomain.preimage g ⟨U,hdom⟩ : M → ℝ)
        (fun x => Q x*H1ComplToLp g U x) := by
      intro α
      exact chartPushed_aeEq_of_ae_eq_riemannianMeasure g α hmeas hmeasq hae
    exact (MemWkpChart_congr_chartPushed_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hc).2 hq
  have hall : ∀ m : ℕ, MemWkpChart (I := I) (M := M) (m+2) 2
      (H1ComplToLp g U : M → ℝ) := by
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
theorem weak_smooth_potential_eigen_smooth_representative (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    ∃ s : SmoothScalar g,
      (H1ComplToLp g U : M → ℝ) =ᵐ[volume g] s.toFun := by
  have hall := weak_smooth_potential_eigen_memWkpChart_all g V lam U hU
  obtain ⟨f,hf,hae⟩ := DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall
    g (H1ComplToLp g U) (fun m => hall (2*m))
  exact ⟨⟨f,hf⟩,hae⟩

/-- The smooth representative satisfies the original pointwise Schrödinger
operator equation, with the actual round Laplacian and actual potential. -/
theorem weak_smooth_potential_eigen_pointwise (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (lam : ℝ)
    (U : H1Compl g)
    (hU : IsWeakPotentialEigenstate g V lam U) :
    ∃ s : SmoothScalar g,
      U = smoothToH1Compl g s ∧
      ∀ x : M,
        -ΔG g s.toContMDiffMap x+V x*s.toFun x = lam*s.toFun x := by
  let Q := smoothEigenSourceFactor g V lam
  obtain ⟨s,hs⟩ := weak_smooth_potential_eigen_smooth_representative g V lam U hU
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
    have hh := weak_smooth_potential_eigen_resolvent g V lam U hU
    rw [hJs] at hh
    exact hh
  have hscalar : s.oneSubLapClassical = T := smoothToLp_injective g (hsrc.trans hmul)
  refine ⟨s,hUs,?_⟩
  intro x
  have he := congrArg (fun f : SmoothScalar g => f.toFun x) hscalar
  change s.toFun x-ΔG g s.toContMDiffMap x = (1+lam-V x)*s.toFun x at he
  nlinarith

end DFLCompactPotential
