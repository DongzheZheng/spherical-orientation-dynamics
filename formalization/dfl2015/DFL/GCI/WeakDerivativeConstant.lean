import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The classical one-dimensional zero-weak-derivative lemma.
The proof is the usual zero-mean test primitive and normalized bump
argument; it is independent of the DFL equation and does not introduce
a substitute Sobolev-space definition. -/

namespace DFL.GCI

open MeasureTheory Set
open scoped Interval Topology ContDiff

noncomputable section

def compactTestPrimitive (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, ψ t

theorem compactTestPrimitive_hasDerivAt (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (x : ℝ) :
    HasDerivAt (compactTestPrimitive ψ) (ψ x) x := by
  have hint : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hc
  have hfun : compactTestPrimitive ψ =
      fun x => (∫ t in Set.Iic (0 : ℝ), ψ t) + ∫ t in (0 : ℝ)..x, ψ t := by
    funext x
    have hi := intervalIntegral.integral_Iic_sub_Iic
      (a := (0 : ℝ)) (b := x) hint.integrableOn hint.integrableOn
    unfold compactTestPrimitive
    linarith
  rw [hfun]
  exact (intervalIntegral.integral_hasDerivAt_right
    hint.intervalIntegrable (hψ.stronglyMeasurableAtFilter volume (𝓝 x))
    hψ.continuousAt).const_add _

theorem compactTestPrimitive_contDiff (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : ContDiff ℝ ∞ (compactTestPrimitive ψ) := by
  have hd (x : ℝ) := compactTestPrimitive_hasDerivAt ψ hψ.continuous hc x
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have hderiv : deriv (compactTestPrimitive ψ) = ψ := by
    funext x
    exact (hd x).deriv
  rw [hderiv]
  exact hψ

theorem compactTestPrimitive_hasCompactSupport (ψ : ℝ → ℝ)
    (hc : HasCompactSupport ψ) (hzero : (∫ t, ψ t) = 0) :
    HasCompactSupport (compactTestPrimitive ψ) := by
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc a b))
  intro x hx
  have hxne : compactTestPrimitive ψ x ≠ 0 := hx
  constructor
  · by_contra hax
    have hxa : x < a := lt_of_not_ge hax
    have hψzero : ∀ t ∈ Set.Iic x, ψ t = 0 := by
      intro t ht
      by_contra hne
      have hmem : t ∈ tsupport ψ := subset_closure hne
      have hat := ha hmem
      exact (not_lt_of_ge (hat.trans ht)).elim hxa
    apply hxne
    unfold compactTestPrimitive
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic] with t ht
    exact hψzero t ht
  · by_contra hxb
    have hbx : b < x := lt_of_not_ge hxb
    have hψzero : ∀ t ∉ Set.Iic x, ψ t = 0 := by
      intro t ht
      by_contra hne
      have hmem : t ∈ tsupport ψ := subset_closure hne
      have htb := hb hmem
      have hxt : x < t := lt_of_not_ge ht
      exact (not_lt_of_ge htb).elim (hbx.trans hxt)
    apply hxne
    unfold compactTestPrimitive
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hψzero, hzero]

/-- A locally integrable real function with vanishing distributional
derivative on the whole line is almost everywhere constant. -/
theorem ae_constant_of_zero_weak_derivative (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x * f x) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  have hmean : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, ψ x) = 0 → (∫ x, ψ x * f x) = 0 := by
    intro ψ hψ hc hzero
    have h := hweak (compactTestPrimitive ψ) (compactTestPrimitive_contDiff ψ hψ hc)
      (compactTestPrimitive_hasCompactSupport ψ hc hzero)
    have hderiv : deriv (compactTestPrimitive ψ) = ψ := by
      funext x
      exact (compactTestPrimitive_hasDerivAt ψ hψ.continuous hc x).deriv
    simpa only [hderiv] using h
  let ρ : ℝ → ℝ := (default : ContDiffBump (0 : ℝ)).normed volume
  have hρ : ContDiff ℝ ∞ ρ := ContDiffBump.contDiff_normed _
  have hcρ : HasCompactSupport ρ := ContDiffBump.hasCompactSupport_normed _
  have hiρ : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hcρ
  have hρone : (∫ x, ρ x) = 1 := ContDiffBump.integral_normed _
  let c : ℝ := ∫ x, ρ x * f x
  refine ⟨c, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hf (locallyIntegrable_const c)
  intro ψ hψ hcψ
  have hiψ : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hcψ
  let m : ℝ := ∫ x, ψ x
  let ψ₀ : ℝ → ℝ := fun x => ψ x - m * ρ x
  have hd₀ : ContDiff ℝ ∞ ψ₀ := hψ.sub (contDiff_const.mul hρ)
  have hc₀ : HasCompactSupport ψ₀ := hcψ.sub (hcρ.mul_left (f := fun _ => m))
  have hzero : (∫ x, ψ₀ x) = 0 := by
    unfold ψ₀
    rw [integral_sub hiψ (hiρ.const_mul m), integral_const_mul, hρone]
    dsimp [m]
    ring
  have h := hmean ψ₀ hd₀ hc₀ hzero
  have hiψf : Integrable (fun x => ψ x * f x) volume := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ
  have hiρf : Integrable (fun x => ρ x * f x) volume := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hcρ
  have hlin : (∫ x, ψ₀ x * f x) = (∫ x, ψ x * f x) - m * c := by
    unfold ψ₀ c
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub hiψf (hiρf.const_mul m), integral_const_mul]
  simp only [smul_eq_mul]
  rw [integral_mul_const]
  rw [hlin] at h
  change (∫ x, ψ x * f x) = m * c
  linarith

end
end DFL.GCI
