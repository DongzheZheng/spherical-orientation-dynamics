import DFL.GCI.InteriorSmoothDensity
import DFL.GCI.IntegralPrimitiveL2
import DFL.GCI.WeakDerivativeConstant

/-! Zero-mean smooth density on the physical interval. A fixed normalized
interior bump corrects the mean, as in the usual proof of `H¹₀` density. -/

namespace DFL.GCI
open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

instance : angularLebesgue.Regular := by
  unfold angularLebesgue
  infer_instance

instance : IsFiniteMeasureOnCompacts angularLebesgue := by infer_instance

theorem angularLebesgue_ae_interior : ∀ᵐ x ∂angularLebesgue, x ∈ Ioo 0 Real.pi := by
  have hmem : ∀ᵐ x ∂angularLebesgue, x ∈ Ioc 0 Real.pi :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [hmem, angularLebesgue.ae_ne Real.pi] with x hx hne
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩

def l2Mean : AngularL2 →L[ℝ] ℝ :=
  innerSL ℝ ((Lp.const 2 angularLebesgue) (1 : ℝ))

theorem l2Mean_eq_integral (q : AngularL2) : l2Mean q = ∫ x, q x ∂angularLebesgue := by
  rw [l2Mean, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 angularLebesgue (1 : ℝ)] with x hx
  rw [hx]
  simp only [Function.const_apply]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp

def interiorMeanBump : ContDiffBump (Real.pi / 2) where
  rIn := Real.pi / 8
  rOut := Real.pi / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Real.pi_pos]

def interiorMeanTest : ℝ → ℝ := interiorMeanBump.normed volume

theorem interiorMeanTest_contDiff : ContDiff ℝ ∞ interiorMeanTest :=
  ContDiffBump.contDiff_normed _

theorem interiorMeanTest_compact : HasCompactSupport interiorMeanTest :=
  ContDiffBump.hasCompactSupport_normed _

theorem interiorMeanTest_support : tsupport interiorMeanTest ⊆ Ioo 0 Real.pi := by
  rw [interiorMeanTest, ContDiffBump.tsupport_normed_eq]
  intro x hx
  have hx' : |x - Real.pi / 2| ≤ Real.pi / 4 := by
    simpa [Metric.mem_closedBall, Real.dist_eq, interiorMeanBump] using hx
  have h := abs_le.mp hx'
  constructor <;> linarith [Real.pi_pos]

theorem interiorMeanTest_integral : (∫ x, interiorMeanTest x) = 1 :=
  ContDiffBump.integral_normed _

theorem interiorTest_integral_eq (g : ℝ → ℝ) (hs : tsupport g ⊆ Ioo 0 Real.pi) :
    (∫ x, g x ∂angularLebesgue) = ∫ x, g x := by
  unfold angularLebesgue
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply Function.notMem_support.mp
  intro hg
  exact hx ⟨(hs (subset_tsupport g hg)).1, (hs (subset_tsupport g hg)).2.le⟩

def interiorMeanLp : AngularL2 :=
  (interiorMeanTest_contDiff.continuous.memLp_of_hasCompactSupport
    (μ := angularLebesgue) interiorMeanTest_compact).toLp interiorMeanTest

theorem interiorMeanLp_ae : (interiorMeanLp : ℝ → ℝ) =ᵐ[angularLebesgue] interiorMeanTest :=
  MemLp.coeFn_toLp _

theorem interiorMeanLp_mean : l2Mean interiorMeanLp = 1 := by
  rw [l2Mean_eq_integral, integral_congr_ae interiorMeanLp_ae,
    interiorTest_integral_eq _ interiorMeanTest_support, interiorMeanTest_integral]

def zeroMeanCorrection : AngularL2 →L[ℝ] AngularL2 :=
  ContinuousLinearMap.id ℝ AngularL2 - l2Mean.smulRight interiorMeanLp

theorem zeroMeanCorrection_apply (q : AngularL2) :
    zeroMeanCorrection q = q - l2Mean q • interiorMeanLp := rfl

theorem zeroMeanCorrection_fix (q : AngularL2) (hq : l2Mean q = 0) :
    zeroMeanCorrection q = q := by simp [zeroMeanCorrection_apply, hq]

theorem zeroMeanCorrection_mean (q : AngularL2) : l2Mean (zeroMeanCorrection q) = 0 := by
  simp [zeroMeanCorrection_apply, interiorMeanLp_mean]

/-- Every angular `L²` function of mean zero has genuine smooth compact
approximants supported in `(0,π)`, also of mean zero. -/
theorem exists_zeroMean_smooth_approx (q : AngularL2) (hq : l2Mean q = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : ℝ → ℝ) (hψ : MemLp ψ 2 angularLebesgue),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo 0 Real.pi ∧
      (∫ x, ψ x) = 0 ∧ ‖q - hψ.toLp ψ‖ < ε := by
  let K := ‖zeroMeanCorrection‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  obtain ⟨g, hc, hs, hd, hg⟩ := exists_contDiff_interior_eLpNorm_sub_le
    angularLebesgue (Ioo 0 Real.pi) isOpen_Ioo angularLebesgue_ae_interior
    q (Lp.memLp q) hδ
  have hm : MemLp g 2 angularLebesgue := hd.continuous.memLp_of_hasCompactSupport hc
  let t : AngularL2 := hm.toLp g
  have ht : ‖q - t‖ ≤ δ := by
    rw [← dist_eq_norm, Lp.dist_def]
    rw [← ENNReal.le_ofReal_iff_toReal_le
      ((Lp.memLp q).sub (Lp.memLp t)).eLpNorm_ne_top hδ.le]
    have heq : ((q : ℝ → ℝ) - (t : ℝ → ℝ)) =ᵐ[angularLebesgue] (q - g) := by
      filter_upwards [hm.coeFn_toLp] with x hx
      simp [t, hx]
    rwa [eLpNorm_congr_ae heq]
  let m := l2Mean t
  let ψ : ℝ → ℝ := fun x => g x - m * interiorMeanTest x
  have hdψ : ContDiff ℝ ∞ ψ := hd.sub (contDiff_const.mul interiorMeanTest_contDiff)
  have hcψ : HasCompactSupport ψ :=
    hc.sub (interiorMeanTest_compact.mul_left (f := fun _ => m))
  have hsψ : tsupport ψ ⊆ Ioo 0 Real.pi := by
    apply (tsupport_sub g (fun x => m * interiorMeanTest x)).trans
    apply union_subset hs
    exact (tsupport_mul_subset_right (f := fun _ => m) (g := interiorMeanTest)).trans
      interiorMeanTest_support
  have hmψ : MemLp ψ 2 angularLebesgue := hdψ.continuous.memLp_of_hasCompactSupport hcψ
  have hψlp : hmψ.toLp ψ = zeroMeanCorrection t := by
    apply Lp.ext
    filter_upwards [hmψ.coeFn_toLp, hm.coeFn_toLp, interiorMeanLp_ae,
      Lp.coeFn_sub t (m • interiorMeanLp), Lp.coeFn_smul m interiorMeanLp]
      with x hψx htx hρx hsub hsmul
    rw [hψx, zeroMeanCorrection_apply, hsub]
    simp only [Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hρx]
    exact congrArg (fun a => a - m * interiorMeanTest x) htx.symm
  refine ⟨ψ, hmψ, hdψ, hcψ, hsψ, ?_, ?_⟩
  · rw [← interiorTest_integral_eq ψ hsψ]
    rw [← integral_congr_ae hmψ.coeFn_toLp, ← l2Mean_eq_integral, hψlp]
    exact zeroMeanCorrection_mean t
  · rw [hψlp, ← zeroMeanCorrection_fix q hq, ← map_sub]
    calc
      ‖zeroMeanCorrection (q - t)‖ ≤ ‖zeroMeanCorrection‖ * ‖q - t‖ :=
        zeroMeanCorrection.le_opNorm _
      _ ≤ ‖zeroMeanCorrection‖ * δ := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ < K * δ := mul_lt_mul_of_pos_right (by dsimp [K]; linarith) hδ
      _ = ε := by dsimp [δ]; exact mul_div_cancel₀ ε hK.ne'

end
end DFL.GCI
