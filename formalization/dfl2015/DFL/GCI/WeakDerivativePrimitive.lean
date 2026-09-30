import DFL.GCI.WeakDerivativeConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! The classical one-dimensional weak-derivative representative theorem.
For a locally integrable pair `f,q`, the standard smooth-test weak
derivative equation forces `f=c+∫₀ˣq` almost everywhere. This is the usual
proof through the zero-weak-derivative lemma, not a Sobolev-space rename. -/

namespace DFL.GCI

open MeasureTheory Set
open scoped Interval Topology ContDiff

noncomputable section

def localPrimitive (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, q t

theorem locallyIntegrable_intervalIntegrable (q : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) (a b : ℝ) : IntervalIntegrable q volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (hq.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc

theorem localPrimitive_continuous (q : ℝ → ℝ) (hq : LocallyIntegrable q volume) :
    Continuous (localPrimitive q) :=
  intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable q hq) 0

theorem localPrimitive_AC (q : ℝ → ℝ) (hq : LocallyIntegrable q volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (localPrimitive q) a b := by
  let A := min (min a b) (0 : ℝ)
  let B := max (max a b) (0 : ℝ)
  have hab : A ≤ B := (min_le_right (min a b) (0 : ℝ)).trans (le_max_right (max a b) (0 : ℝ))
  have h0 : (0 : ℝ) ∈ Set.uIcc A B := by
    rw [Set.uIcc_of_le hab]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hac := (locallyIntegrable_intervalIntegrable q hq A B).absolutelyContinuousOnInterval_intervalIntegral h0
  apply hac.mono
  rw [Set.uIcc_of_le hab]
  intro x hx
  rw [Set.uIcc] at hx
  dsimp [A, B]
  exact ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩

private theorem compact_test_pair_integrable (f φ : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x * f x) volume := by
  simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hφ hc

/-- Integration by parts for the actual primitive and every smooth
compactly supported test on the whole real line. -/
theorem localPrimitive_distributional_derivative (q : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, deriv φ x * localPrimitive q x) = -(∫ x, φ x * q x) := by
  have hdc := hc.deriv
  have hcompact : IsCompact (tsupport φ ∪ tsupport (deriv φ)) := hc.isCompact.union hdc.isCompact
  obtain ⟨L, hL⟩ := hcompact.bddBelow
  obtain ⟨U, hU⟩ := hcompact.bddAbove
  let a := min L (0 : ℝ) - 1
  let b := max U (0 : ℝ) + 1
  have ha0 : a < 0 := by dsimp [a]; linarith [min_le_right L (0 : ℝ)]
  have hb0 : 0 < b := by dsimp [b]; linarith [le_max_right U (0 : ℝ)]
  have hab : a ≤ b := ha0.le.trans hb0.le
  have hL' : a < L := by dsimp [a]; linarith [min_le_left L (0 : ℝ)]
  have hU' : U < b := by dsimp [b]; linarith [le_max_left U (0 : ℝ)]
  have hout : ∀ x, (x ≤ a ∨ b < x) → φ x = 0 ∧ deriv φ x = 0 := by
    intro x hx
    constructor <;> by_contra hne
    · have hm : x ∈ tsupport φ ∪ tsupport (deriv φ) := Or.inl (subset_closure hne)
      have hl := hL hm
      have hu := hU hm
      rcases hx with hx | hx <;> linarith
    · have hm : x ∈ tsupport φ ∪ tsupport (deriv φ) := Or.inr (subset_closure hne)
      have hl := hL hm
      have hu := hU hm
      rcases hx with hx | hx <;> linarith
  have hφa : φ a = 0 := (hout a (Or.inl le_rfl)).1
  have hφb : φ b = 0 := by
    by_contra hne
    have hm : b ∈ tsupport φ ∪ tsupport (deriv φ) := Or.inl (subset_closure hne)
    exact (not_lt_of_ge (hU hm)).elim hU'
  have hφAC : AbsolutelyContinuousOnInterval φ a b := by
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    obtain ⟨K, hK⟩ := hφ1.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc a b) isCompact_Icc
    apply (show LipschitzOnWith K φ (Set.uIcc a b) from ?_).absolutelyContinuousOnInterval
    simpa only [Set.uIcc_of_le hab] using hK
  have hiq := locallyIntegrable_intervalIntegrable q hq a b
  have hqae := hiq.ae_hasDerivAt_integral
  have h0 : (0 : ℝ) ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact ⟨ha0.le, hb0.le⟩
  have hderiv :
      (∫ x in a..b, φ x * deriv (localPrimitive q) x) = ∫ x in a..b, φ x * q x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with x hx hxab
    have hxab' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hxab
    have hd : deriv (localPrimitive q) x = q x := (hx hxab' 0 h0).deriv
    rw [hd]
  have hibp := hφAC.integral_mul_deriv_eq_deriv_mul (localPrimitive_AC q hq a b)
  have hibp' :
      (∫ x in a..b, φ x * q x) = -(∫ x in a..b, deriv φ x * localPrimitive q x) := by
    rw [hderiv] at hibp
    simpa only [hφa, hφb, zero_mul, sub_zero, zero_sub] using hibp
  have hpall : (∫ x in a..b, deriv φ x * localPrimitive q x) =
      ∫ x, deriv φ x * localPrimitive q x := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ≤ a ∨ b < x := by simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hx
    rw [(hout x hx').2, zero_mul]
  have hqall : (∫ x in a..b, φ x * q x) = ∫ x, φ x * q x := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ≤ a ∨ b < x := by simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hx
    rw [(hout x hx').1, zero_mul]
  rw [hpall, hqall] at hibp'
  linarith

/-- The usual one-dimensional representative theorem: a locally
integrable function whose distributional weak derivative is `q` agrees
almost everywhere with the actual absolutely continuous primitive plus
a constant. The test class is the conventional `C_c∞(ℝ)`. -/
theorem ae_eq_constant_add_primitive_of_weak_derivative
    (f q : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hq : LocallyIntegrable q volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x * f x) = -(∫ x, φ x * q x)) :
    ∃ c : ℝ, f =ᵐ[volume] fun x => c + localPrimitive q x := by
  have hp : LocallyIntegrable (localPrimitive q) volume := (localPrimitive_continuous q hq).locallyIntegrable
  have hdiff : LocallyIntegrable (fun x => f x - localPrimitive q x) volume := hf.sub hp
  obtain ⟨c, hc⟩ := ae_constant_of_zero_weak_derivative (fun x => f x - localPrimitive q x)
    hdiff (by
      intro φ hφ hcompact
      have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
      have hi1 := compact_test_pair_integrable f (deriv φ) hf hdφ.continuous hcompact.deriv
      have hi2 := compact_test_pair_integrable (localPrimitive q) (deriv φ) hp hdφ.continuous hcompact.deriv
      simp_rw [mul_sub]
      rw [integral_sub hi1 hi2, hweak φ hφ hcompact,
        localPrimitive_distributional_derivative q hq φ hφ hcompact]
      ring)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  linarith

end
end DFL.GCI
