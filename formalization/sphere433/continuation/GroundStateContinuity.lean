import continuation.RoundSpherePositiveGround
import continuation.PotentialMinimumDependence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! Compactness and simplicity imply continuity of the actual normalized
positive ground. No continuity or differentiability of an eigenbranch is an input. -/
noncomputable section
set_option maxHeartbeats 1600000
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

namespace DFLGroundContinuity
section Abstract
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

/-- The compact form embedding and the actual resolvent identity give a
convergent subsequence of normalized eigenstates in the entire form norm. -/
theorem normalized_eigenstates_subseq (J : H →L[ℝ] L) (hJ : IsCompactOperator J)
    (R : L →L[ℝ] H) (P : ℕ → L →L[ℝ] L) (P₀ : L →L[ℝ] L)
    (lam : ℕ → ℝ) (lam₀ : ℝ) (U : ℕ → H)
    (hP : Tendsto P atTop (𝓝 P₀)) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hn : ∀ n, ‖J (U n)‖ = 1)
    (hweak : ∀ n v, DFLSphere.potentialForm J (P n) (U n) v = lam n*⟪J (U n),J v⟫_ℝ)
    (hR : ∀ n, U n = R ((1+lam n) • J (U n)-P n (J (U n)))) :
    ∃ (φ : ℕ → ℕ) (W : H), StrictMono φ ∧ Tendsto (U ∘ φ) atTop (𝓝 W) ∧
      ‖J W‖ = 1 ∧ ∀ v, DFLSphere.potentialForm J P₀ W v = lam₀*⟪J W,J v⟫_ℝ := by
  obtain ⟨C₁,hC₁⟩ := (isBounded_range_of_tendsto P hP).exists_norm_le
  obtain ⟨C₂,hC₂⟩ := (isBounded_range_of_tendsto lam hlam).exists_norm_le
  have hb (n : ℕ) : ‖U n‖^2 ≤ C₁+C₂+1 := by
    have hh := hweak n (U n)
    unfold DFLSphere.potentialForm at hh
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hn] at hh
    have hp : |⟪P n (J (U n)),J (U n)⟫_ℝ| ≤ ‖P n‖ := by
      calc
        _ ≤ ‖P n (J (U n))‖*‖J (U n)‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖P n‖*‖J (U n)‖)*‖J (U n)‖ :=
          mul_le_mul_of_nonneg_right ((P n).le_opNorm _) (norm_nonneg _)
        _ = ‖P n‖ := by rw [hn]; ring
    have h₁ := hC₁ (P n) (mem_range_self n)
    have h₂ := hC₂ (lam n) (mem_range_self n)
    have hLam := le_abs_self (lam n)
    have hp' := (abs_le.mp hp).1
    simp only [Real.norm_eq_abs] at h₂
    norm_num at hh
    linarith
  let C := |C₁+C₂+1|+1
  have hUb : ∀ n, U n ∈ closedBall (0 : H) C := by
    intro n
    rw [mem_closedBall_zero_iff]
    have hc := le_abs_self (C₁+C₂+1)
    have ha := abs_nonneg (C₁+C₂+1)
    dsimp only [C]
    nlinarith [hb n,norm_nonneg (U n)]
  obtain ⟨K,hK,hJK⟩ := hJ.image_closedBall_subset_compact C
  obtain ⟨v,_,φ,hφ,hv⟩ := hK.tendsto_subseq (fun n => hJK ⟨U n,hUb n,rfl⟩)
  let W := R ((1+lam₀) • v-P₀ v)
  have hPφ := hP.comp hφ.tendsto_atTop
  have hLamPhi := hlam.comp hφ.tendsto_atTop
  have hPv : Tendsto (fun n => P (φ n) (J (U (φ n)))) atTop (𝓝 (P₀ v)) := by
    have ht := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := L) (F := L)).continuous.tendsto (P₀,v)
    exact ht.comp (hPφ.prodMk_nhds hv)
  have hsource := (((tendsto_const_nhds (x := (1 : ℝ))).add hLamPhi).smul hv).sub hPv
  have hU : Tendsto (U ∘ φ) atTop (𝓝 W) := by
    have hh := R.continuous.tendsto ((1+lam₀) • v-P₀ v) |>.comp hsource
    convert hh using 1
    funext n
    exact hR (φ n)
  have hJW : J W = v :=
    tendsto_nhds_unique (J.continuous.tendsto W |>.comp hU) hv
  have hnorm : ‖J W‖ = 1 := by
    have hh := hv.norm
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖v‖) := by
      convert hh using 1
      funext n
      exact (hn (φ n)).symm
    rw [hJW]
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨φ,W,hφ,hU,hnorm,?_⟩
  intro z
  have hleft := ((hU.inner (𝕜 := ℝ) (tendsto_const_nhds (x := z))).sub
    (hv.inner (𝕜 := ℝ) (tendsto_const_nhds (x := J z)))).add
    (hPv.inner (𝕜 := ℝ) (tendsto_const_nhds (x := J z)))
  have hright := hLamPhi.mul (hv.inner (𝕜 := ℝ) (tendsto_const_nhds (x := J z)))
  have hleft' : Tendsto (fun n => lam (φ n)*⟪J (U (φ n)),J z⟫_ℝ) atTop
      (𝓝 (DFLSphere.potentialForm J P₀ W z)) := by
    convert hleft using 1
    · funext n
      exact (hweak (φ n) z).symm
    · unfold DFLSphere.potentialForm
      rw [hJW]
  rw [hJW]
  exact tendsto_nhds_unique hleft' hright
end Abstract
end DFLGroundContinuity

namespace DFLSphere
private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- Continuous potentials act continuously in operator norm on actual L². -/
def roundContinuousPotentialOperator (k : ℕ) : C(RoundSphere k,ℝ) →L[ℝ]
    (Lp ℝ 2 (roundVolume k) →L[ℝ] Lp ℝ 2 (roundVolume k)) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (roundVolume k) ∞ 2 2).comp
    (ContinuousMap.toLp ∞ (roundVolume k) ℝ)

theorem roundContinuousPotentialOperator_eq (k : ℕ) (V : C(RoundSphere k,ℝ))
    (hV : MemLp (V : RoundSphere k → ℝ) ∞ (roundVolume k)) :
    roundContinuousPotentialOperator k V = boundedPotentialMultiplication V hV := by
  change ((ContinuousLinearMap.mul ℝ ℝ).holderL (roundVolume k) ∞ 2 2)
      (ContinuousMap.toLp ∞ (roundVolume k) ℝ V) =
    ((ContinuousLinearMap.mul ℝ ℝ).holderL (roundVolume k) ∞ 2 2) (hV.toLp V)
  congr 1

/-- The genuine smooth positive normalized ground at the variational minimum. -/
theorem positiveGround_exists (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ∃ u : SmoothScalar (roundSphereMetric k),
      ‖smoothToLp (roundSphereMetric k) u‖ = 1 ∧ (∀ x, 0 < u.toFun x) ∧
      roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) u) = roundPotentialMinimum k V ∧
      (∀ W : H1Compl (roundSphereMetric k),
        roundPotentialMinimum k V*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      ∀ x, -ΔG (roundSphereMetric k) u.toContMDiffMap x+V x*u.toFun x =
        roundPotentialMinimum k V*u.toFun x := by
  obtain ⟨lam,u,hn,hpos,he,hmin,hpoint⟩ := round_positive_smooth_potential_ground_exists k V
  obtain ⟨W,hWn,hWe,hWmin⟩ := roundPotentialMinimum_minimizer k V V.contMDiff.continuous
  have h₁ := hmin W
  rw [hWn,hWe] at h₁
  have h₂ := hWmin (smoothToH1Compl (roundSphereMetric k) u)
  rw [H1ComplToLp_smoothToH1Compl,hn,he] at h₂
  have hv : roundPotentialMinimum k V = lam := by norm_num at h₁ h₂; linarith
  exact ⟨u,hn,hpos,he.trans hv.symm,hv.symm ▸ hmin,hv.symm ▸ hpoint⟩

def positiveGround (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    SmoothScalar (roundSphereMetric k) := (positiveGround_exists k V).choose

theorem positiveGround_spec (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
      ‖smoothToLp (roundSphereMetric k) (positiveGround k V)‖ = 1 ∧
      (∀ x, 0 < (positiveGround k V).toFun x) ∧
      roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) (positiveGround k V)) =
        roundPotentialMinimum k V ∧
      (∀ W : H1Compl (roundSphereMetric k),
        roundPotentialMinimum k V*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      ∀ x, -ΔG (roundSphereMetric k) (positiveGround k V).toContMDiffMap x+
        V x*(positiveGround k V).toFun x = roundPotentialMinimum k V*(positiveGround k V).toFun x :=
  (positiveGround_exists k V).choose_spec

/-- The actual operator form equals the original weak potential form. -/
theorem roundContinuousPotentialOperator_form (k : ℕ) (V : C(RoundSphere k,ℝ))
    (U W : H1Compl (roundSphereMetric k)) :
    potentialForm (H1ComplToLp (roundSphereMetric k)) (roundContinuousPotentialOperator k V) U W =
      ⟪U,W⟫_ℝ-⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ+
        ∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*
          H1ComplToLp (roundSphereMetric k) W x ∂roundVolume k := by
  have hV : MemLp (V : RoundSphere k → ℝ) ∞ (roundVolume k) :=
    V.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [roundContinuousPotentialOperator_eq k V hV]
  unfold potentialForm
  rw [boundedPotentialMultiplication_inner]

/-- The bare resolvent identity for an actual continuous potential. -/
theorem round_weak_potential_resolvent_operator (k : ℕ) (V : C(RoundSphere k,ℝ))
    (lam : ℝ) (U : H1Compl (roundSphereMetric k))
    (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    U = resolvent (roundSphereMetric k)
      ((1+lam) • H1ComplToLp (roundSphereMetric k) U-
        roundContinuousPotentialOperator k V (H1ComplToLp (roundSphereMetric k) U)) := by
  let J := H1ComplToLp (roundSphereMetric k)
  let P := roundContinuousPotentialOperator k V
  apply ext_inner_right ℝ
  intro W
  rw [resolvent_inner_eq_lpFunctional,inner_sub_right,real_inner_smul_right]
  have hw := hU W
  have hp : ⟪J W,P (J U)⟫_ℝ =
      ∫ x, V x*J U x*J W x ∂roundVolume k := by
    have hf := roundContinuousPotentialOperator_form k V U W
    unfold potentialForm at hf
    have hcomm : ⟪J W,P (J U)⟫_ℝ = ⟪P (J U),J W⟫_ℝ := real_inner_comm _ _
    rw [hcomm]
    linarith
  have hcomm : ⟪J W,J U⟫_ℝ = ⟪J U,J W⟫_ℝ := real_inner_comm _ _
  rw [hp,hcomm]
  change ⟪U,W⟫_ℝ-⟪J U,J W⟫_ℝ+
    (∫ x, V x*J U x*J W x ∂roundVolume k) = lam*⟪J U,J W⟫_ℝ at hw
  linarith

/-- Continuous bundle of the actual smooth potential. -/
def continuousOfSmoothPotential (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    C(RoundSphere k,ℝ) := ⟨V,V.contMDiff.continuous⟩

theorem positiveGround_weak (k : ℕ) (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    IsRoundWeakPotentialEigenstate k V (roundPotentialMinimum k V)
      (smoothToH1Compl (roundSphereMetric k) (positiveGround k V)) := by
  have hs := positiveGround_spec k V
  apply round_potential_minimizer_weak k V V.contMDiff.continuous
  · rw [hs.2.2.1,H1ComplToLp_smoothToH1Compl,hs.1]
    ring
  · exact hs.2.2.2.1

/-- The actual normalized positive ground is continuous in the entire H¹
completion norm when the smooth potentials converge in continuous sup norm.
Compactness is supplied by the real sphere Rellich theorem; the limit is
identified by the proved full weak eigenspace simplicity and positivity. -/
theorem positiveGround_tendsto_of_potential_tendsto (k : ℕ)
    (V : ℕ → C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯)
    (V₀ : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯)
    (hV : Tendsto (fun n => continuousOfSmoothPotential k (V n)) atTop
      (𝓝 (continuousOfSmoothPotential k V₀))) :
    Tendsto (fun n => smoothToH1Compl (roundSphereMetric k) (positiveGround k (V n))) atTop
      (𝓝 (smoothToH1Compl (roundSphereMetric k) (positiveGround k V₀))) := by
  let g := roundSphereMetric k
  let J := H1ComplToLp g
  let P := fun n => roundContinuousPotentialOperator k (continuousOfSmoothPotential k (V n))
  let P₀ := roundContinuousPotentialOperator k (continuousOfSmoothPotential k V₀)
  let lam := fun n => roundPotentialMinimum k (V n)
  let lam₀ := roundPotentialMinimum k V₀
  let U := fun n => smoothToH1Compl g (positiveGround k (V n))
  let U₀ := smoothToH1Compl g (positiveGround k V₀)
  have hP : Tendsto P atTop (𝓝 P₀) :=
    (roundContinuousPotentialOperator k).continuous.tendsto _ |>.comp hV
  have hl : Tendsto lam atTop (𝓝 lam₀) :=
    (roundPotentialMinimum_continuous k).tendsto _ |>.comp hV
  have hnorm : ∀ n, ‖J (U n)‖ = 1 := by
    intro n
    rw [H1ComplToLp_smoothToH1Compl]
    exact (positiveGround_spec k (V n)).1
  have hweak : ∀ n W, potentialForm J (P n) (U n) W = lam n*⟪J (U n),J W⟫_ℝ := by
    intro n W
    rw [roundContinuousPotentialOperator_form]
    exact positiveGround_weak k (V n) W
  have hres : ∀ n, U n = resolvent g ((1+lam n) • J (U n)-P n (J (U n))) := by
    intro n
    exact round_weak_potential_resolvent_operator k (continuousOfSmoothPotential k (V n))
      (lam n) (U n) (positiveGround_weak k (V n))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ,W,hφ,hW,hnW,hwW⟩ := DFLGroundContinuity.normalized_eigenstates_subseq J
    (H1ComplToLp_isCompactOperator g) (resolvent g) (P ∘ ns) P₀ (lam ∘ ns) lam₀ (U ∘ ns)
    (hP.comp hns) (hl.comp hns) (fun n => hnorm (ns n)) (fun n z => hweak (ns n) z)
      (fun n => hres (ns n))
  have hWe : IsRoundWeakPotentialEigenstate k V₀ lam₀ W := by
    intro z
    have hh := hwW z
    rw [roundContinuousPotentialOperator_form] at hh
    exact hh
  have hs₀ := positiveGround_spec k V₀
  obtain ⟨c,hc⟩ := round_positive_potential_weak_eigenspace_simple k V₀ lam₀
    (positiveGround k V₀) hs₀.2.1 hs₀.2.2.2.2 W hWe
  have hn₀ : ‖J U₀‖ = 1 := by rw [H1ComplToLp_smoothToH1Compl]; exact hs₀.1
  have hcn : |c| = 1 := by
    rw [hc,map_smul,norm_smul,hn₀,Real.norm_eq_abs,mul_one] at hnW
    exact hnW
  have hpair : ∀ n, 0 ≤ ⟪J (U n),J U₀⟫_ℝ := by
    intro n
    rw [H1ComplToLp_smoothToH1Compl,H1ComplToLp_smoothToH1Compl,L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [(positiveGround k (V n)).memLp_two.coeFn_toLp,
      (positiveGround k V₀).memLp_two.coeFn_toLp] with x hx hy
    have hxn : (smoothToLp g (positiveGround k (V n)) : RoundSphere k → ℝ) x =
      (positiveGround k (V n)).toFun x := hx
    have hx₀ : (smoothToLp g (positiveGround k V₀) : RoundSphere k → ℝ) x =
      (positiveGround k V₀).toFun x := hy
    simp only [hxn,hx₀,RCLike.inner_apply,conj_trivial]
    exact mul_nonneg (hs₀.2.1 x).le ((positiveGround_spec k (V n)).2.1 x).le
  have hlim := (J.continuous.tendsto W |>.comp hW).inner (𝕜 := ℝ) (tendsto_const_nhds (x := J U₀))
  have hnn : 0 ≤ ⟪J W,J U₀⟫_ℝ := ge_of_tendsto hlim (Eventually.of_forall (fun n => hpair (ns (φ n))))
  have hcnonneg : 0 ≤ c := by
    rw [hc,map_smul,real_inner_smul_left,real_inner_self_eq_norm_sq,hn₀] at hnn
    norm_num at hnn
    exact hnn
  have hc1 : c = 1 := by rw [abs_of_nonneg hcnonneg] at hcn; exact hcn
  have hWU : W = U₀ := by rw [hc,hc1,one_smul]
  refine ⟨φ,?_⟩
  rw [hWU] at hW
  exact hW

end DFLSphere
